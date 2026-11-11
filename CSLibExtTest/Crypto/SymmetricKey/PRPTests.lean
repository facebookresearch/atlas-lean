/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.SymmetricKey.PRP
public import Mathlib.Data.ZMod.Basic

/-!
# Tests for pseudorandom permutations and the switching lemma

`X = ZMod 3`. The distinguisher `collide` queries `0` and `1` and outputs whether the answers
agree.

* Against a random function it outputs `1` with probability `9 / 27 = 1/3`; against a random
  permutation never. Its switching advantage is `1/3`, which is exactly
  `collisionProb (ZMod 3) 2 = 1 - (3 * 2) / 3 ^ 2`: the switching lemma's bound is attained, so a
  smaller bound would be false.
* The shift family `k ↦ (· + k)` has PRP advantage `0` against `collide`, but PRF advantage `1/3`:
  `prfAdvantage_le` is tight here too.
* Asymptotic notions: the constant shift family is `PRPSecure` against `collide`, but not
  `Cslib.Crypto.PRF.PRFSecure` (the PRF API's notion, which `prfSecure_of_prpSecure` concludes):
  its PRF advantage is the constant `1/3`, so the birthday hypothesis of `prfSecure_of_prpSecure`
  cannot be dropped. The family keyed by the random function itself is `PRFSecure` against every
  distinguisher.
-/

@[expose] public section

namespace Cslib.Crypto.PRPTests

open Cslib.Crypto.Framework Cslib.Crypto.PRP Cslib.Crypto.PRF

/-- Query `0` and `1` and output whether the answers agree. -/
def collide : Unit → OracleComp (ZMod 3) (ZMod 3) Bool :=
  fun _ => .query 0 fun y₀ => .query 1 fun y₁ => .done (decide (y₀ = y₁))

theorem collide_queryBounded : ∀ s, FreeM.IsQueryBounded 2 (collide s) :=
  fun _ _ _ => trivial

theorem winProb_prfRand_collide : winProb (prfRand collide) = 1 / 3 := by
  rw [prfRand, winProb_map_uniform]
  have hc : (Finset.univ.filter fun ω : (ZMod 3 → ZMod 3) × Unit =>
      (collide ω.2).run ω.1 = true).card = 9 := by decide
  rw [hc]
  simp only [Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_unit]
  norm_num

theorem prpRand_collide : prpRand collide = PMF.pure false := by
  rw [prpRand, ← PMF.map_const (Cslib.Probability.PMF.uniformOfFintype
    (Equiv.Perm (ZMod 3) × Unit)) false]
  congr 1
  funext ω
  change decide (ω.1 0 = ω.1 1) = false
  simp only [decide_eq_false_iff_not, ω.1.injective.eq_iff]
  decide

theorem collisionProb_three_two : Cslib.Crypto.Birthday.collisionProb (ZMod 3) 2 = 1 / 3 := by
  rw [Cslib.Crypto.Birthday.collisionProb_eq]
  norm_num [Nat.descFactorial]

/-- The switching advantage of `collide` attains the bound `collisionProb (ZMod 3) 2`. -/
theorem advantage_collide :
    advantage (prfRand collide) (prpRand collide) = Cslib.Crypto.Birthday.collisionProb (ZMod 3) 2 := by
  rw [advantage, winProb_prfRand_collide, prpRand_collide, winProb_pure, collisionProb_three_two]
  norm_num

example : advantage (prfRand collide) (prpRand collide) ≤
    Cslib.Crypto.Birthday.collisionProb (ZMod 3) 2 :=
  abs_prfRand_sub_prpRand_le collide collide_queryBounded

example : advantage (prfRand collide) (prpRand collide) ≤ 2 * (2 - 1) / (2 * 3) := by
  have := abs_prfRand_sub_prpRand_le_birthday (q := 2) collide collide_queryBounded
  simpa using this

/-- The shift family. -/
def shift (k : ZMod 3) : Equiv.Perm (ZMod 3) := Equiv.addRight k

theorem prpReal_shift_collide : prpReal shift collide = PMF.pure false := by
  rw [prpReal, ← PMF.map_const (Cslib.Probability.PMF.uniformOfFintype (ZMod 3 × Unit)) false]
  congr 1
  funext ω
  revert ω
  decide

/-- The shift family is indistinguishable from a random permutation by `collide`. -/
theorem prpAdvantage_shift_collide : prpAdvantage shift collide = 0 := by
  rw [prpAdvantage, prpReal_shift_collide, prpRand_collide, advantage_self]

/-- But its PRF advantage is `1/3`, and `prfAdvantage_le` gives exactly that bound. -/
theorem prfAdvantage_shift_collide : prfAdvantage (fun k => ⇑(shift k)) collide = 1 / 3 := by
  have h : prfAdvantage (fun k => ⇑(shift k)) collide =
      advantage (prpReal shift collide) (prfRand collide) := rfl
  rw [h, advantage, prpReal_shift_collide, winProb_pure, winProb_prfRand_collide]
  norm_num

example : prfAdvantage (fun k => ⇑(shift k)) collide ≤ 0 + 1 / 3 := by
  have := prfAdvantage_le shift collide collide_queryBounded
  rwa [prpAdvantage_shift_collide, collisionProb_three_two] at this

/-- The constant shift family is PRP-secure against the distinguisher family `collide`. -/
theorem prpSecure_shift :
    PRPSecure (fun (_ : ℕ) => shift)
      (fun D : (n : ℕ) → Unit → OracleComp (ZMod 3) (ZMod 3) Bool => ∀ n, D n = collide) :=
  fun D hD => negligibleAdv_zero.mono fun n => by
    dsimp only
    rw [hD n, prpAdvantage_shift_collide]

/-- The constant shift family is **not** PRF-secure (`Cslib.Crypto.PRF.PRFSecure`) against
`collide`: its PRF advantage is the constant `1/3`. With `|X n| = 3` the birthday term does not
vanish, so `prfSecure_of_prpSecure` does not apply, and this shows its conclusion fails. -/
theorem not_prfSecure_shift :
    ¬ Cslib.Crypto.PRF.PRFSecure (fun (_ : ℕ) k => ⇑(shift k))
      (fun D : (n : ℕ) → Unit → OracleComp (ZMod 3) (ZMod 3) Bool => ∀ n, D n = collide) := by
  intro h
  refine not_negligibleAdv_const (δ := 1 / 3) (by norm_num)
    ((h (fun _ => collide) fun _ => rfl).mono fun n => ?_)
  dsimp only
  rw [prfAdvantage_shift_collide]

/-- The family keyed by the random function itself has PRF advantage `0`. -/
theorem prfAdvantage_self_keyed (D : Unit → OracleComp (ZMod 3) (ZMod 3) Bool) :
    prfAdvantage (fun k : ZMod 3 → ZMod 3 => k) D = 0 := by
  rw [prfAdvantage, show prfReal (fun k : ZMod 3 → ZMod 3 => k) D = prfRand D from rfl, sub_self,
    abs_zero]

/-- Hence it is `Cslib.Crypto.PRF.PRFSecure` against every distinguisher family. -/
example : Cslib.Crypto.PRF.PRFSecure (fun (_ : ℕ) (k : ZMod 3 → ZMod 3) => k)
    (fun _ : (n : ℕ) → Unit → OracleComp (ZMod 3) (ZMod 3) Bool => True) :=
  fun D _ => negligibleAdv_zero.mono fun n => (prfAdvantage_self_keyed (D n)).le

end Cslib.Crypto.PRPTests

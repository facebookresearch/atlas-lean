/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.BrauerArithmeticCompletion
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# The arithmetic completion `lim_n M/nM`

Residues, reductions and the unit are computed on `ℤ`. The completion of `ℤ`
is nonzero on `1`, while the completion of the divisible group `ℚ` is trivial,
as `lim_n ℚ/nℚ = 0`. The induced maps respect identities and composition.
-/

noncomputable section

namespace MathlibExtTest.BrauerArithmeticCompletion

open AlgebraicGeometry.BrauerArithmeticCompletion

/-! ## Multiples, residues and reductions -/

example (n : ℕ) (a : ℤ) : multiplication ℤ n a = n • a := rfl

example : multiples ℤ 0 = ⊥ := by
  ext a
  simp [multiples, multiplication]

example : multiples ℤ 1 = ⊤ := by
  ext a
  simp only [AddSubgroup.mem_top, iff_true]
  exact ⟨a, by simp [multiplication]⟩

example : multiples ℤ 4 ≤ multiples ℤ 2 := multiples_le ℤ (by norm_num)

example : (QuotientAddGroup.mk 7 : Mod ℤ 6) = QuotientAddGroup.mk 1 := by
  rw [QuotientAddGroup.eq]
  exact ⟨-1, by norm_num [multiplication]⟩

example : transition ℤ (by norm_num : 2 ∣ 6) (QuotientAddGroup.mk 5) = QuotientAddGroup.mk 1 := by
  change (QuotientAddGroup.mk 5 : Mod ℤ 2) = QuotientAddGroup.mk 1
  rw [QuotientAddGroup.eq]
  exact ⟨-2, by norm_num [multiplication]⟩

/-! ## The unit and projections -/

example (n : Modulus) (a : ℤ) : projection ℤ n (unit ℤ a) = QuotientAddGroup.mk a := rfl

/-- The completion of `ℤ` does not kill `1`. -/
example : unit ℤ 1 ≠ 0 := by
  intro h
  have h2 := congrArg (projection ℤ ⟨2, by norm_num⟩) h
  rw [map_zero] at h2
  change (QuotientAddGroup.mk 1 : Mod ℤ 2) = 0 at h2
  obtain ⟨b, hb⟩ := (QuotientAddGroup.eq_zero_iff _).mp h2
  change (2 : ℕ) • b = 1 at hb
  rw [nsmul_eq_mul] at hb
  omega

/-- The completion of the divisible group `ℚ` is trivial. -/
example (x : Completion ℚ) : x = 0 := by
  ext n
  obtain ⟨q, hq⟩ := QuotientAddGroup.mk_surjective (x.val n)
  change x.val n = 0
  rw [← hq, QuotientAddGroup.eq_zero_iff]
  refine ⟨q / n.val, ?_⟩
  change n.val • (q / n.val) = q
  have hn : (n.val : ℚ) ≠ 0 := by exact_mod_cast n.2.ne'
  rw [nsmul_eq_mul]
  field_simp

/-! ## Evaluations killed by a modulus -/

private def mod3 : ℤ →+ ZMod 3 := Int.castAddHom _

private theorem mod3_killed (a : ℤ) : (⟨3, by norm_num⟩ : Modulus).val • mod3 a = 0 := by
  have h3 : (3 : ZMod 3) = 0 := by decide
  simp [mod3, nsmul_eq_mul, h3]

example : liftKilled ℤ mod3 ⟨3, by norm_num⟩ mod3_killed (QuotientAddGroup.mk 5) = 2 := by
  change mod3 5 = 2
  decide

example : completedEvaluation ℤ mod3 ⟨3, by norm_num⟩ mod3_killed (unit ℤ (-1)) = 2 := by
  rw [completedEvaluation_unit]
  decide

/-! ## Induced maps -/

example (a : ℤ) : map (multiplication ℤ 2) (unit ℤ a) = unit ℤ (2 • a) := by
  simp [multiplication]

example (n : ℕ) (a : ℤ) :
    modMap (multiplication ℤ 2) n (QuotientAddGroup.mk a) = QuotientAddGroup.mk (2 • a) := rfl

example (x : Completion ℤ) : map (AddMonoidHom.id ℤ) x = x := by
  ext n
  obtain ⟨a, ha⟩ := QuotientAddGroup.mk_surjective (x.val n)
  change modMap (AddMonoidHom.id ℤ) n.val (x.val n) = x.val n
  rw [← ha]
  rfl

example {A B C : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : A →+ B) (g : B →+ C) (x : Completion A) : map (g.comp f) x = map g (map f x) := by
  ext n
  obtain ⟨a, ha⟩ := QuotientAddGroup.mk_surjective (x.val n)
  change modMap (g.comp f) n.val (x.val n) = modMap g n.val (modMap f n.val (x.val n))
  rw [← ha]
  rfl

end MathlibExtTest.BrauerArithmeticCompletion

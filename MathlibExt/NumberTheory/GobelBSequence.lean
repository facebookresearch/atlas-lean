/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GobelNonIntegrality
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The periodic Göbel sign sequence

For even $l$ and $2s+1$ coprime to $l+1$, the two reflection laws and the normalization
at index one determine a unique periodic sign sequence.
-/

namespace MetaMathlibExt
namespace existsUnique_gobelBSequence

private theorem exists_sequence (l s : ℕ) (hleven : Even l)
    (hcoprime : Nat.Coprime (2 * s + 1) (l + 1)) :
    ∃ b : ℤ → ℤ, IsGobelBSequence l s b := by
  -- Measure each residue in steps of −(2s+1), a generator modulo l+1.
  let u := ZMod.unitOfCoprime (2 * s + 1) hcoprime
  let r (n : ℤ) : ZMod (l + 1) := -(↑u⁻¹ * (n : ZMod (l + 1)))
  let b (n : ℤ) : ℤ := if (r n).val % 2 = (r 1).val % 2 then 1 else -1
  have hmod : ((l : ZMod (l + 1)) + 1) = 0 := by
    exact_mod_cast ZMod.natCast_self (l + 1)
  have hrperiod : Function.Periodic r (l + 1 : ℤ) := by
    intro n
    simp [r, Int.cast_add, hmod]
  obtain ⟨k, hk⟩ := hleven
  refine ⟨b, fun n => ?_, fun n => ?_, ?_, fun n hn => ?_, fun n => ?_⟩
  · simp only [b]
    split <;> simp
  · simp only [b, hrperiod n]
  · simp [b]
  · change n % (l + 1 : ℤ) ≠ 0 at hn
    have hn' : (n : ZMod (l + 1)) ≠ 0 := by
      simpa only [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_iff_emod_eq_zero,
        Nat.cast_add, Nat.cast_one] using hn
    have hr : r n ≠ 0 := by simpa [r] using hn'
    have hneg : r ((l + 1 : ℤ) - n) = -r n := by simp [r, hmod]
    have hlt := (r n).val_lt
    simp only [b, hneg, ZMod.neg_val, ite_eq_right hr]
    split <;> split <;> omega
  · -- The second reflection sends coordinate x to −1−x, whose representative is l−x.val.
    have hu : (↑u⁻¹ : ZMod (l + 1)) * (2 * (s : ZMod (l + 1)) + 1) = 1 := by
      simp [u, ZMod.coe_unitOfCoprime]
    have href : r ((s : ℤ) + 1 + n) = -1 - r ((s : ℤ) - n) := by
      simp only [r, Int.cast_add, Int.cast_sub, Int.cast_natCast, Int.cast_one]
      linear_combination -hu
    have hlt := (r ((s : ℤ) - n)).val_lt
    have hle : (r ((s : ℤ) - n)).val ≤ (-1 : ZMod (l + 1)).val := by
      rw [ZMod.val_neg_one]
      omega
    have hparity : (r ((s : ℤ) + 1 + n)).val % 2 = (r ((s : ℤ) - n)).val % 2 := by
      rw [href, ZMod.val_sub hle, ZMod.val_neg_one]
      omega
    simp only [b, hparity]

private theorem unique_sequence {l s : ℕ} (hcoprime : Nat.Coprime (2 * s + 1) (l + 1))
    {b c : ℤ → ℤ} (hb : IsGobelBSequence l s b) (hc : IsGobelBSequence l s c) : b = c := by
  -- Agreement is preserved by both reflections, hence by translation through 2s+1.
  let P (n : ℤ) := b n = c n
  have hp : Function.Periodic P (l + 1 : ℤ) := by
    intro n
    simp only [P, hb.2.1, hc.2.1]
  have hneg (n : ℤ) : P (-n) = P n := by
    by_cases hn : n % (l + 1 : ℤ) = 0
    · obtain ⟨k, hk⟩ := Int.dvd_iff_emod_eq_zero.mpr hn
      rw [hk, mul_comm]
      simpa only [Int.cast_id] using (hp.int_mul k).neg_eq.trans (hp.int_mul k).eq.symm
    · rw [← hp.sub_eq' (x := n)]
      change (_ = _) = (b n = c n)
      rw [hb.2.2.2.1 n hn, hc.2.2.2.1 n hn, neg_inj]
  have hstep : Function.Periodic P (2 * s + 1 : ℤ) := by
    intro n
    have reflect {f : ℤ → ℤ} (hf : IsGobelBSequence l s f) :
        f (n + (2 * s + 1 : ℤ)) = f (-n) := by
      convert (hf.2.2.2.2 ((s : ℤ) + n)).symm using 1 <;> congr 1 <;> ring
    change (b _ = c _) = (b n = c n)
    rw [reflect hb, reflect hc]
    exact hneg n
  obtain ⟨u, v, huv⟩ := hcoprime.isCoprime
  push_cast at huv
  have hp₁ : Function.Periodic P 1 := huv ▸ (hstep.int_mul u).add_period (hp.int_mul v)
  funext n
  have hn : P n = P 0 := by simpa only [mul_one, Int.cast_id] using hp₁.int_mul_eq n
  exact hn.mpr (hp₁.eq.mp (hb.2.2.1.trans hc.2.2.1.symm))

end existsUnique_gobelBSequence

set_option linter.unusedVariables false in
/-- **Existence and uniqueness of the sequence $b_{l,s}$.** Let $l$ be an even natural number and
$s$ a natural number with $s \le l$ such that $2s + 1$ and $l + 1$ are coprime. Then exactly one
function $b : \mathbb{Z} \to \mathbb{Z}$ satisfies the defining conditions of $b_{l,s}$:
$b(n) = \pm 1$ for every integer $n$, $b(n + l + 1) = b(n)$ for every $n$, $b(1) = 1$,
$b(n) = -b(l + 1 - n)$ for every $n$ not divisible by $l + 1$, and $b(s - n) = b(s + 1 + n)$ for
every $n$.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on
Non-Integrality of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 29 (2026), Article
26.3.8, Proposition 20. -/
public theorem existsUnique_gobelBSequence
    (l s : ℕ) (hleven : Even l) (hs : s ≤ l) (hcoprime : Nat.Coprime (2 * s + 1) (l + 1)) :
    ∃! b : ℤ → ℤ, IsGobelBSequence l s b := by
  obtain ⟨b, hb⟩ := existsUnique_gobelBSequence.exists_sequence l s hleven hcoprime
  exact ⟨b, hb, fun c hc => existsUnique_gobelBSequence.unique_sequence hcoprime hc hb⟩

end MetaMathlibExt

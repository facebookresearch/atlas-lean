/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Equivalence.PowerloopResults
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-!
# Analytic bound for one transcribed node power

The `powerloop` result is one plus the first zero-based quotient-bit position
at which the doubled midpoints differ.  This file turns that exact discrete
characterization into the real logarithmic estimate used by the
Munro--Wild merge-cost argument.
-/

namespace CPythonListsort

/-- The scaled midpoint quotient whose binary low bit is inspected by
`powerloopQuotientBit`. -/
def powerScaledQuotient (x n k : Nat) : Nat :=
  2 ^ k * x / n

@[simp]
theorem powerScaledQuotient_mod_two (x n k : Nat) :
    powerScaledQuotient x n k % 2 = powerloopQuotientBit x n k := by
  rfl

/-- Removing the low bit from the next scaled quotient recovers the previous
scaled quotient. -/
theorem powerScaledQuotient_succ_div_two (x n k : Nat) :
    powerScaledQuotient x n (k + 1) / 2 =
      powerScaledQuotient x n k := by
  unfold powerScaledQuotient
  rw [Nat.div_div_eq_div_mul, pow_succ]
  have htwo : 0 < (2 : Nat) := by omega
  calc
    2 ^ k * 2 * x / (n * 2) =
        2 * (2 ^ k * x) / (2 * n) := by
      congr 1 <;> ring
    _ = 2 ^ k * x / n := Nat.mul_div_mul_left (2 ^ k * x) n htwo

/-- For doubled midpoint coordinates in `[0,2n)`, agreement of all quotient
bits through position `k` determines the complete scaled quotient at `k`. -/
theorem powerScaledQuotient_eq_of_bits_eq_up_to
    {x y n k : Nat} (hx : x < 2 * n) (hy : y < 2 * n)
    (hbits : ∀ j ≤ k,
      powerloopQuotientBit x n j = powerloopQuotientBit y n j) :
    powerScaledQuotient x n k = powerScaledQuotient y n k := by
  induction k with
  | zero =>
      have hn : 0 < n := by omega
      have hxq : powerScaledQuotient x n 0 < 2 := by
        simpa [powerScaledQuotient] using
          (Nat.div_lt_iff_lt_mul hn).2 hx
      have hyq : powerScaledQuotient y n 0 < 2 := by
        simpa [powerScaledQuotient] using
          (Nat.div_lt_iff_lt_mul hn).2 hy
      have hmod :
          powerScaledQuotient x n 0 % 2 =
            powerScaledQuotient y n 0 % 2 := by
        rw [powerScaledQuotient_mod_two,
          powerScaledQuotient_mod_two]
        exact hbits 0 (by omega)
      rwa [Nat.mod_eq_of_lt hxq, Nat.mod_eq_of_lt hyq] at hmod
  | succ k ih =>
      have hprior : ∀ j ≤ k,
          powerloopQuotientBit x n j =
            powerloopQuotientBit y n j := by
        intro j hj
        exact hbits j (by omega)
      have hdiv :
          powerScaledQuotient x n (k + 1) / 2 =
            powerScaledQuotient y n (k + 1) / 2 := by
        rw [powerScaledQuotient_succ_div_two,
          powerScaledQuotient_succ_div_two]
        exact ih hprior
      have hmod :
          powerScaledQuotient x n (k + 1) % 2 =
            powerScaledQuotient y n (k + 1) % 2 := by
        rw [powerScaledQuotient_mod_two,
          powerScaledQuotient_mod_two]
        exact hbits (k + 1) (by omega)
      have hxsplit :=
        Nat.mod_add_div (powerScaledQuotient x n (k + 1)) 2
      have hysplit :=
        Nat.mod_add_div (powerScaledQuotient y n (k + 1)) 2
      omega

/-- If two doubled midpoint coordinates first differ at bit `k > 0`, their
distance still fits strictly inside one depth-`k-1` quotient cell. -/
theorem gap_pow_lt_of_firstDifferingQuotientBit
    {a b n k : Nat} (ha : a < b) (hb : b < 2 * n)
    (hk : IsFirstDifferingQuotientBit a b n k) (hkpos : 0 < k) :
    2 ^ (k - 1) * (b - a) < n := by
  have hn : 0 < n := by omega
  have haBound : a < 2 * n := by omega
  have hbits : ∀ j ≤ k - 1,
      powerloopQuotientBit a n j = powerloopQuotientBit b n j := by
    intro j hj
    exact hk.2.2 j (by omega)
  have hquot := powerScaledQuotient_eq_of_bits_eq_up_to
    haBound hb hbits
  let scale := 2 ^ (k - 1)
  have hscale : 0 < scale := by positivity
  have hscaledLt : scale * a < scale * b :=
    Nat.mul_lt_mul_of_pos_left ha hscale
  have haDecompose := Nat.div_add_mod (scale * a) n
  have hbDecompose := Nat.div_add_mod (scale * b) n
  have haMod : (scale * a) % n < n := Nat.mod_lt _ hn
  have hbMod : (scale * b) % n < n := Nat.mod_lt _ hn
  change scale * a / n = scale * b / n at hquot
  let quotient := scale * a / n
  have haQuotient : scale * a / n = quotient := rfl
  have hbQuotient : scale * b / n = quotient := hquot.symm
  rw [haQuotient] at haDecompose
  rw [hbQuotient] at hbDecompose
  have hscaledGap : scale * (b - a) = scale * b - scale * a := by
    exact Nat.mul_sub_left_distrib scale b a
  have hsub :
      scale * b - scale * a =
        (scale * b) % n - (scale * a) % n := by
    omega
  rw [hscaledGap, hsub]
  omega

/-- A first-differing-bit power is strictly below the logarithmic inverse-gap
bound with the exact additive constant used by PowerSort. -/
theorem firstDifferingPower_lt_logb_gap_add_two
    {a b n k leafLength : Nat}
    (ha : a < b) (hb : b < 2 * n)
    (hk : IsFirstDifferingQuotientBit a b n k)
    (hleaf : 0 < leafLength) (hleafN : leafLength ≤ n)
    (hleafGap : leafLength ≤ b - a) :
    ((k + 1 : Nat) : Real) <
      Real.logb 2 ((n : Real) / (leafLength : Real)) + 2 := by
  have hn : 0 < n := by omega
  have hnReal : (0 : Real) < n := by exact_mod_cast hn
  have hleafReal : (0 : Real) < leafLength := by exact_mod_cast hleaf
  by_cases hkzero : k = 0
  · subst k
    have hratio : (1 : Real) ≤ (n : Real) / (leafLength : Real) := by
      apply (le_div_iff₀ hleafReal).2
      simpa using (show (leafLength : Real) ≤ n by exact_mod_cast hleafN)
    have hlog : 0 ≤ Real.logb 2 ((n : Real) / (leafLength : Real)) :=
      Real.logb_nonneg (by norm_num) hratio
    norm_num
    linarith
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hkzero
    have hgap := gap_pow_lt_of_firstDifferingQuotientBit ha hb hk hkpos
    have hpowLeaf : 2 ^ (k - 1) * leafLength < n := by
      exact lt_of_le_of_lt (Nat.mul_le_mul_left _ hleafGap) hgap
    have hratioPos : (0 : Real) < (n : Real) / (leafLength : Real) :=
      div_pos hnReal hleafReal
    have hrpow :
        (2 : Real) ^ ((k - 1 : Nat) : Real) <
          (n : Real) / (leafLength : Real) := by
      rw [Real.rpow_natCast]
      apply (lt_div_iff₀ hleafReal).2
      exact_mod_cast hpowLeaf
    have hlog :
        ((k - 1 : Nat) : Real) <
          Real.logb 2 ((n : Real) / (leafLength : Real)) :=
      (Real.lt_logb_iff_rpow_lt (by norm_num) hratioPos).2 hrpow
    have hkCast : ((k : Nat) : Real) = ((k - 1 : Nat) : Real) + 1 := by
      have hkNat : k = (k - 1) + 1 := by omega
      exact_mod_cast hkNat
    push_cast
    rw [hkCast]
    linarith

/-- The concrete finite-width `powerloop` result obeys the same logarithmic
bound for either positive component of its midpoint gap. -/
theorem powerloop_lt_logb_component_add_two
    (s1 n1 n2 n : PySSize) (leafLength : Nat)
    (hvalid : ValidPowerloopInput s1 n1 n2 n)
    (hleaf : 0 < leafLength)
    (hleafGap : leafLength ≤ n1.toNat + n2.toNat) :
    (powerloop s1 n1 n2 n : Real) <
      Real.logb 2 ((n.toNat : Real) / (leafLength : Real)) + 2 := by
  have hresult := powerloopResult s1 n1 n2 n hvalid
  dsimp only at hresult
  rcases hresult with ⟨_, k, _, hpower, hk⟩
  have hbounds := powerloopInputBounds s1 n1 n2 n hvalid
  dsimp only at hbounds
  rcases hbounds with ⟨_, hab, hb, _, _, _, _⟩
  have hgap :
      (2 * s1.toNat + n1.toNat + n1.toNat + n2.toNat) -
          (2 * s1.toNat + n1.toNat) =
        n1.toNat + n2.toNat := by
    omega
  rw [hpower]
  have hleafN : leafLength ≤ n.toNat := by
    have hsum := hvalid.2.2.2.2.2.2.1
    omega
  apply firstDifferingPower_lt_logb_gap_add_two hab hb hk hleaf hleafN
  rwa [hgap]

end CPythonListsort

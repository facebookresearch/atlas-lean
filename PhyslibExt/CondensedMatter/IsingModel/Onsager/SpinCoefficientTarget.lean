/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Onsager.SpinCharacter
public import PhyslibExt.CondensedMatter.IsingModel.Onsager.SpinPolynomial

/-!

# The spin Kac-Ward identities as determinant identities

Restating the spin Kac-Ward identities as `(character sum)² = det (1 - twisted Kac-Ward matrix)`.

## i. Overview

The twisted Kac-Ward determinant with spin phases equals the sector determinant `ons_spinDetX`, and
the character sums are the signed sector sums. So the spin Kac-Ward identities at `x` say exactly
that, for each spin structure `(a, b)`, the square of the character-weighted even-subgraph sum is
the twisted Kac-Ward determinant.

## ii. Key results

- `ons_KWmatPhase_det_eq_spinDetX` : the twisted determinant is the sector determinant
- `ons_spinCoefficientIdentity` : the identities in determinant form
- `ons_spinKacWardAt_iff_coefficientIdentity` : equivalence of the two forms

## iii. Table of contents

- A. The determinant form

## iv. References

- M. Kac and J. C. Ward, *A combinatorial solution of the two-dimensional Ising model*, Phys. Rev.
  88 (1952) 1332-1337
- D. Cimasoni, *A generalized Kac-Ward formula*, J. Stat. Mech. (2010) P07023

-/

@[expose] public section

namespace StatMech.Onsager

open Matrix BigOperators

/-! ## A. The determinant form -/

lemma ons_KWmatPhase_det_eq_spinDetX (L : ℕ) [NeZero L] [Fact (1 < L)]
    (x : ℝ) (a b : Fin 2) :
    (1 - ons_KWmatPhase L (x : ℂ) ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b)).det =
        (ons_spinDetX L x a b : ℂ) := by
  rw [ons_KWmatPhase_det_eq_prod L (x : ℂ) ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) (ons_spaceRoot L)
    ons_turnRoot_sq (ons_spaceRoot_primitive L (NeZero.ne L))
    (ons_spinPhase_ne_zero L a) (ons_spinPhase_ne_zero L b)]
  have hfactor : ∀ i j : ℕ,
      ((1 + (x : ℂ) ^ 2) ^ 2 -
        (x : ℂ) * (1 - (x : ℂ) ^ 2) *
          (ons_spinPhase L a * ons_spaceRoot L ^ i +
            (ons_spinPhase L a * ons_spaceRoot L ^ i)⁻¹ +
            (ons_spinPhase L b * ons_spaceRoot L ^ j +
              (ons_spinPhase L b * ons_spaceRoot L ^ j)⁻¹))) =
        (((1 + x ^ 2) ^ 2 - 2 * x * (1 - x ^ 2) *
          (Real.cos (2 * Real.pi * (i + (a.val : ℝ) / 2) / L) +
            Real.cos (2 * Real.pi * (j + (b.val : ℝ) / 2) / L)) : ℝ) : ℂ) := by
    intro i j
    rw [ons_spinPhase_spaceRoot_cos, ons_spinPhase_spaceRoot_cos]
    norm_cast
    ring
  let F : ℕ → ℕ → ℂ := fun i j =>
    (((1 + x ^ 2) ^ 2 - 2 * x * (1 - x ^ 2) *
      (Real.cos (2 * Real.pi * ((i : ℝ) + (a.val : ℝ) / 2) / L) +
        Real.cos (2 * Real.pi * ((j : ℝ) + (b.val : ℝ) / 2) / L)) : ℝ) : ℂ)
  let G : (ZMod L × ZMod L) → ℂ := fun z =>
    ((1 + (x : ℂ) ^ 2) ^ 2 -
      (x : ℂ) * (1 - (x : ℂ) ^ 2) *
        (ons_spinPhase L a * ons_spaceRoot L ^ z.1.val +
          (ons_spinPhase L a * ons_spaceRoot L ^ z.1.val)⁻¹ +
          (ons_spinPhase L b * ons_spaceRoot L ^ z.2.val +
            (ons_spinPhase L b * ons_spaceRoot L ^ z.2.val)⁻¹)))
  change (∏ z, G z) = _
  calc
    (∏ z, G z) = (∏ z : ZMod L × ZMod L, F z.1.val z.2.val) := by
      apply Finset.prod_congr rfl
      intro z _
      unfold G F
      exact hfactor z.1.val z.2.val
    _ = ∏ i ∈ Finset.range L, ∏ j ∈ Finset.range L, F i j :=
      prod_zmod_prod_eq_prod_range L F
    _ = (ons_spinDetX L x a b : ℂ) := by
      unfold F ons_spinDetX
      norm_cast

/-- For every spin structure `(a, b)`, the square of the spin-character sum equals the twisted
Kac-Ward determinant `det (1 - Λ_{ab})` at activity `x`. -/
def ons_spinCoefficientIdentity (L : ℕ) [Fact (2 < L)] (x : ℝ) : Prop :=
  ∀ a b : Fin 2,
    (ons_spinCharacterSum L x a b : ℂ) ^ 2 =
      (1 - ons_KWmatPhase L (x : ℂ) ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b)).det

lemma ons_spinKacWardAt_iff_coefficientIdentity
    (L : ℕ) [NeZero L] [Fact (2 < L)] (x : ℝ) :
    ons_spinKacWardAt L x ↔ ons_spinCoefficientIdentity L x := by
  let : Fact (1 < L) := ⟨by have := (Fact.out : 2 < L); omega⟩
  unfold ons_spinKacWardAt ons_spinCoefficientIdentity
  constructor
  · rintro ⟨h00, h10, h01, h11⟩ a b
    fin_cases a <;> fin_cases b
    · change (ons_spinCharacterSum L x 0 0 : ℂ) ^ 2 = _
      rw [ons_KWmatPhase_det_eq_spinDetX,
        ons_spinCharacterSum_zero_zero]
      exact_mod_cast h00
    · change (ons_spinCharacterSum L x 0 1 : ℂ) ^ 2 = _
      rw [ons_KWmatPhase_det_eq_spinDetX,
        ons_spinCharacterSum_zero_one]
      exact_mod_cast h01
    · change (ons_spinCharacterSum L x 1 0 : ℂ) ^ 2 = _
      rw [ons_KWmatPhase_det_eq_spinDetX,
        ons_spinCharacterSum_one_zero]
      exact_mod_cast h10
    · change (ons_spinCharacterSum L x 1 1 : ℂ) ^ 2 = _
      rw [ons_KWmatPhase_det_eq_spinDetX,
        ons_spinCharacterSum_one_one]
      exact_mod_cast h11
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hh := h 0 0
      rw [ons_KWmatPhase_det_eq_spinDetX,
        ons_spinCharacterSum_zero_zero] at hh
      exact_mod_cast hh
    · have hh := h 1 0
      rw [ons_KWmatPhase_det_eq_spinDetX,
        ons_spinCharacterSum_one_zero] at hh
      exact_mod_cast hh
    · have hh := h 0 1
      rw [ons_KWmatPhase_det_eq_spinDetX,
        ons_spinCharacterSum_zero_one] at hh
      exact_mod_cast hh
    · have hh := h 1 1
      rw [ons_KWmatPhase_det_eq_spinDetX,
        ons_spinCharacterSum_one_one] at hh
      exact_mod_cast hh

end StatMech.Onsager

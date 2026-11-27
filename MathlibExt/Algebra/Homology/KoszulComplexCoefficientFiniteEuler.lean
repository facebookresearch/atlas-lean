/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.KoszulComplexCoefficientAnnihilation
public import MathlibExt.Algebra.Homology.KoszulComplexCoefficientEulerAdditive

/-!
# Finite-length Euler characteristics for Koszul tensor complexes

For a finite coefficient module, finite length of the module-annihilator
quotient gives finite homology lengths of its Koszul tensor complex. The
finite exterior rank gives eventual vanishing. These data define the
alternating sum of homology lengths.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u v

namespace KoszulComplex

variable (R : Type u) [CommRing R] [IsNoetherianRing R] {n : ℕ}

/-- Genuine finite-length homology data for an original Koszul coefficient tensor complex. -/
def familyTensorCoefficientFiniteLength
    (a : Fin n → R) (M : ModuleCat.{v} R) [Module.Finite R M]
    (hquot : Module.length R
      (R ⧸ (Ideal.span (Set.range a) ⊔ Module.annihilator R M)) ≠ ⊤) :
    HomologicalComplex.FiniteLengthHomologyData R (familyTensorCoefficientComplex R a M) where
  cutoff := n + 1
  length_ne_top j _ := familyTensorCoefficient_homology_length_ne_top R a M hquot j
  vanishes j hj :=
    (HomologicalComplex.ExactAt.of_isZero
      (familyTensorCoefficientComplex_isZero_above R a M j (Nat.lt_of_succ_le hj))).isZero_homology

/-- The original Koszul coefficient Euler invariant. -/
def familyTensorCoefficientEuler
    (a : Fin n → R) (M : ModuleCat.{v} R) [Module.Finite R M]
    (hquot : Module.length R
      (R ⧸ (Ideal.span (Set.range a) ⊔ Module.annihilator R M)) ≠ ⊤) : ℤ :=
  HomologicalComplex.finiteLengthEulerCharacteristic R
    (familyTensorCoefficientFiniteLength R a M hquot)

/-- The actual bounded alternating homology sum includes every original degree. -/
theorem familyTensorCoefficientEuler_eq
    (a : Fin n → R) (M : ModuleCat.{v} R) [Module.Finite R M]
    (hquot : Module.length R
      (R ⧸ (Ideal.span (Set.range a) ⊔ Module.annihilator R M)) ≠ ⊤) :
    familyTensorCoefficientEuler R a M hquot =
      ∑ j ∈ Finset.range (n + 1), (-1 : ℤ) ^ j *
        (Module.length R ((familyTensorCoefficientComplex R a M).homology j)).toNat := rfl

end KoszulComplex

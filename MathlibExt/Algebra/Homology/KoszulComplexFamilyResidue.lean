/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.Algebra.Homology.KoszulComplexProjectiveLift
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Residue targets for finite-family Koszul complexes

When a finite family spans the maximal ideal of a local ring, its Koszul
augmentation quotient is canonically the residue field. This file gives both
the algebra equivalence and the exact universe-lifted `ModuleCat` isomorphism
used by projective-resolution comparison maps.

No regularity, positive-degree Koszul exactness, minimality, or projective-
dimension statement is asserted.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe u v

namespace KoszulComplex

variable (R : Type u) [CommRing R] [IsLocalRing R]
variable {I : Type v} [Fintype I]

/-- A finite family spanning the maximal ideal has maximal family ideal. -/
theorem familyIdeal_eq_maximalIdeal (a : I → R)
    (hspan : Ideal.span (Set.range a) = IsLocalRing.maximalIdeal R) :
    ideal R (I → R) (familyFunctional R a) =
      IsLocalRing.maximalIdeal R :=
  (familyIdeal_eq_span R a).trans hspan

private theorem familyIdeal_eq_ker_residue (a : I → R)
    (hspan : Ideal.span (Set.range a) = IsLocalRing.maximalIdeal R) :
    ideal R (I → R) (familyFunctional R a) =
      RingHom.ker
        (Algebra.ofId R (IsLocalRing.ResidueField R)).toRingHom := by
  rw [familyIdeal_eq_maximalIdeal R a hspan]
  change IsLocalRing.maximalIdeal R =
    RingHom.ker (algebraMap R (IsLocalRing.ResidueField R))
  rw [IsLocalRing.ResidueField.algebraMap_eq,
    IsLocalRing.ker_residue]

/-- The quotient by a finite family spanning the maximal ideal is the
residue field, as an `R`-algebra. -/
@[no_expose]
def familyQuotientResidueAlgEquiv (a : I → R)
    (hspan : Ideal.span (Set.range a) = IsLocalRing.maximalIdeal R) :
    (R ⧸ ideal R (I → R) (familyFunctional R a)) ≃ₐ[R]
      IsLocalRing.ResidueField R :=
  (Ideal.quotientEquivAlgOfEq R
    (familyIdeal_eq_ker_residue R a hspan)).trans
      (Ideal.quotientKerAlgEquivOfSurjective
        (f := Algebra.ofId R (IsLocalRing.ResidueField R))
        (by
          change Function.Surjective
            (algebraMap R (IsLocalRing.ResidueField R))
          rw [IsLocalRing.ResidueField.algebraMap_eq]
          exact IsLocalRing.residue_surjective (R := R)))

/-- On representatives, the family quotient equivalence is the residue map. -/
@[simp]
theorem familyQuotientResidueAlgEquiv_mk (a : I → R)
    (hspan : Ideal.span (Set.range a) = IsLocalRing.maximalIdeal R)
    (r : R) :
    familyQuotientResidueAlgEquiv R a hspan
        (Ideal.Quotient.mk
          (ideal R (I → R) (familyFunctional R a)) r) =
      IsLocalRing.residue R r := by
  rfl

/-- The exact universe-lifted quotient target of the Koszul augmentation is
isomorphic to the lifted residue-field object. -/
@[no_expose]
def familyQuotientResidueIso (a : I → R)
    (hspan : Ideal.span (Set.range a) = IsLocalRing.maximalIdeal R) :
    familyAugmentationTarget R a ≅
      (ModuleCat.uliftFunctor.{max u v, u} R).obj
        (ModuleCat.of R (IsLocalRing.ResidueField R)) :=
  (ModuleCat.uliftFunctor.{max u v, u} R).mapIso
    (familyQuotientResidueAlgEquiv R a hspan).toLinearEquiv.toModuleIso

/-- The lifted quotient/residue isomorphism sends a lifted quotient
representative to the lifted residue class. -/
@[simp]
theorem familyQuotientResidueIso_hom_up_mk (a : I → R)
    (hspan : Ideal.span (Set.range a) = IsLocalRing.maximalIdeal R)
    (r : R) :
    (familyQuotientResidueIso R a hspan).hom.hom
        (ULift.up (Ideal.Quotient.mk
          (ideal R (I → R) (familyFunctional R a)) r)) =
      ULift.up (IsLocalRing.residue R r) := by
  change ULift.up (familyQuotientResidueAlgEquiv R a hspan
    (Ideal.Quotient.mk _ r)) = _
  rw [familyQuotientResidueAlgEquiv_mk]

end KoszulComplex

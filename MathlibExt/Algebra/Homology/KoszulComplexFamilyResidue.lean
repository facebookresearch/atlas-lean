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
# The residue-field target of a finite-family Koszul augmentation

For a local ring R and a finite family spanning its maximal ideal, the family quotient R/(a)
is canonically the residue field. The algebra comparison sends the class of r to its residue.

Lifting this comparison gives the exact module isomorphism from the Koszul augmentation target
to the displayed lifted residue coefficient, with the ring and index universe heights
retained.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe u v

namespace KoszulComplex

variable (R : Type u) [CommRing R] [IsLocalRing R]
variable {I : Type v} [Fintype I]

/-- The ideal of a maximal-ideal generating family.

If the family spans the maximal ideal, its Koszul family ideal equals that maximal ideal. -/
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

/-- The family quotient algebra identified with the residue field.

For a maximal-ideal spanning family, R modulo its Koszul ideal is R-algebra equivalent to the
residue field. -/
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

/-- The residue algebra comparison on a quotient class.

The class of r is sent to residue R r. -/
@[simp]
theorem familyQuotientResidueAlgEquiv_mk (a : I → R)
    (hspan : Ideal.span (Set.range a) = IsLocalRing.maximalIdeal R)
    (r : R) :
    familyQuotientResidueAlgEquiv R a hspan
        (Ideal.Quotient.mk
          (ideal R (I → R) (familyFunctional R a)) r) =
      IsLocalRing.residue R r := by
  rfl

/-- The lifted module isomorphism of the family quotient target.

The Koszul augmentation target is isomorphic to the displayed universe lift of the
residue-field module. -/
@[no_expose]
def familyQuotientResidueIso (a : I → R)
    (hspan : Ideal.span (Set.range a) = IsLocalRing.maximalIdeal R) :
    familyAugmentationTarget R a ≅
      (ModuleCat.uliftFunctor.{max u v, u} R).obj
        (ModuleCat.of R (IsLocalRing.ResidueField R)) :=
  (ModuleCat.uliftFunctor.{max u v, u} R).mapIso
    (familyQuotientResidueAlgEquiv R a hspan).toLinearEquiv.toModuleIso

/-- The lifted residue comparison on an inserted class.

The forward comparison sends up(r mod the family ideal) to up(residue r). -/
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

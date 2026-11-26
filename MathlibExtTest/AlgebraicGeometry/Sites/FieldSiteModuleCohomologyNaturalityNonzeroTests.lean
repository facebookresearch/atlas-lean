/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Sites.FieldSiteModuleCohomologyNaturality
public import MathlibExt.CategoryTheory.Action.Trivial
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsSepClosed

/-!
# Nonzero coefficients in the field-site degree-zero comparison

Let `K` be the algebraic closure of `ℚ`, viewed as its own separable closure.
The coefficient group is `ULift.{1} ℤ`, with trivial `Gal(K/K)`-action. Thus
the field lies in universe zero and the coefficients in universe one.

The inverse sheaf of this module has the canonical constant global section
represented by one. Its actual degree-zero derived global-section class
maps through the field-site continuous-cohomology comparison, the zero-degree
invariant comparison, and the sheaf/Galois counit to the same coefficient one.
The coefficient map `x ↦ x+x` induces a sheaf map and two naturality routes.
Both routes have coefficient two, which is nonzero and differs from one.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme.DerivedSections

namespace MathlibExtTest.AlgebraicGeometry.Sites.FieldSiteNonzero

private abbrev K := AlgebraicClosure ℚ

private abbrev Coeff := ULift.{1} ℤ

private abbrev coefficients : AddCommGrpCat.{1} := AddCommGrpCat.of Coeff

private abbrev G := Gal(K/K)

private abbrev M : FieldCohomologyModule.{0, 1} K K :=
  DiscreteAbelianAction.trivialObject G coefficients

private abbrev Q : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{1} :=
  (fieldInvariantSkyscraperInverseSheaf.{0, 1} K K).obj M

private abbrev Γ :
    Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{1} ⥤ AddCommGrpCat.{1} :=
  Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{1}

private abbrev T := fieldGeometricStalkGaloisFunctor.{0, 1} K K

private abbrev H₀ := fieldContinuousCohomologyFunctor.{0, 1} K K 0

private abbrev ε : T.obj Q ⟶ M :=
  (fieldSheafGaloisEquivalence.{0, 1} K K).counitIso.hom.app M

private abbrev β : H₀.obj (T.obj Q) ⟶
    DiscreteAbelianAction.invariantsFunctor.obj (T.obj Q) :=
  (fieldContinuousCohomologyZeroIso.{0, 1} K K).hom.app (T.obj Q)

private abbrev comparison : (Γ.rightDerived 0).obj Q ⟶ H₀.obj (T.obj Q) :=
  (fieldDerivedSectionsContinuousCohomologyIso.{0, 1} K K 0).hom.app Q

private def double : Coeff →+ Coeff :=
  AddMonoidHom.id Coeff + AddMonoidHom.id Coeff

private abbrev doubleCoefficient : coefficients ⟶ coefficients :=
  AddCommGrpCat.ofHom double

private abbrev μ : M ⟶ M :=
  DiscreteAbelianAction.trivialMap G doubleCoefficient

private abbrev τ : Q ⟶ Q :=
  (fieldInvariantSkyscraperInverseSheaf.{0, 1} K K).map μ

private def invariant (n : ℤ) : DiscreteAbelianAction.invariantsFunctor.obj M :=
  (DiscreteAbelianAction.trivialInvariantsEquiv G coefficients).symm (ULift.up n)

private def constantSection (n : ℤ) : Γ.obj Q :=
  fieldInvariantConstantGlobalSection.{0, 1} K K M (invariant n)

private def sourceClass (n : ℤ) : (Γ.rightDerived 0).obj Q :=
  (Γ.rightDerivedZeroIsoSelf.inv.app Q) (constantSection n)

private def nativeClass (n : ℤ) : H₀.obj (T.obj Q) := comparison (sourceClass n)

private def invariantCoordinate :
    DiscreteAbelianAction.invariantsFunctor.obj (T.obj Q) →+ Coeff :=
  (DiscreteAbelianAction.trivialInvariantsEquiv G coefficients).toAddMonoidHom.comp
    (DiscreteAbelianAction.invariantsFunctor.map ε).hom

private def sectionCoordinate : Γ.obj Q →+ Coeff :=
  invariantCoordinate.comp ((fieldGlobalSectionsInvariantsIso.{0, 1} K K).hom.app Q).hom

private def nativeCoordinate : H₀.obj (T.obj Q) →+ Coeff :=
  invariantCoordinate.comp β.hom

private lemma constantSection_coordinate (n : ℤ) :
    sectionCoordinate (constantSection n) = ULift.up n := by
  change DiscreteAbelianAction.trivialInvariantsEquiv G coefficients
    (DiscreteAbelianAction.invariantsFunctor.map ε
      ((fieldGlobalSectionsInvariantsIso.{0, 1} K K).hom.app Q
        (fieldInvariantConstantGlobalSection.{0, 1} K K M (invariant n)))) = ULift.up n
  exact (congrArg (DiscreteAbelianAction.trivialInvariantsEquiv G coefficients)
    (fieldGlobalSectionsInvariants_counit_constant.{0, 1} K K M (invariant n))).trans
      ((DiscreteAbelianAction.trivialInvariantsEquiv G coefficients).apply_symm_apply _)

private lemma comparison_coordinate (x : (Γ.rightDerived 0).obj Q) :
    nativeCoordinate (comparison x) =
      sectionCoordinate ((Γ.rightDerivedZeroIsoSelf.hom.app Q) x) := by
  have h := fieldGammaContinuousIso_zero.{0, 1} K K Q
  have hx : β (comparison x) =
      (fieldGlobalSectionsInvariantsIso.{0, 1} K K).hom.app Q
        ((Γ.rightDerivedZeroIsoSelf.hom.app Q) x) :=
    ConcreteCategory.congr_hom h x
  exact congrArg invariantCoordinate hx

private lemma nativeClass_coordinate (n : ℤ) :
    nativeCoordinate (nativeClass n) = ULift.up n := by
  change nativeCoordinate (comparison (sourceClass n)) = ULift.up n
  rw [comparison_coordinate]
  have h : (Γ.rightDerivedZeroIsoSelf.hom.app Q) (sourceClass n) = constantSection n :=
    ConcreteCategory.congr_hom (Γ.rightDerivedZeroIsoSelf.app Q).inv_hom_id
      (constantSection n)
  rw [h]
  exact constantSection_coordinate n

private lemma nativeCoordinate_map (x : H₀.obj (T.obj Q)) :
    nativeCoordinate ((H₀.map (T.map τ)) x) = double (nativeCoordinate x) := by
  have hβ : β ((H₀.map (T.map τ)) x) =
      DiscreteAbelianAction.invariantsFunctor.map (T.map τ) (β x) :=
    ConcreteCategory.congr_hom
      ((fieldContinuousCohomologyZeroIso.{0, 1} K K).hom.naturality (T.map τ)) x
  have hε : T.map τ ≫ ε = ε ≫ μ :=
    (fieldSheafGaloisEquivalence.{0, 1} K K).counitIso.hom.naturality μ
  have hi :
      DiscreteAbelianAction.invariantsFunctor.map (T.map τ) ≫
          DiscreteAbelianAction.invariantsFunctor.map ε =
        DiscreteAbelianAction.invariantsFunctor.map ε ≫
          DiscreteAbelianAction.invariantsFunctor.map μ := by
    simpa only [Functor.map_comp] using
      congrArg (fun f : T.obj Q ⟶ M => DiscreteAbelianAction.invariantsFunctor.map f) hε
  have hix :
      DiscreteAbelianAction.invariantsFunctor.map ε
          (DiscreteAbelianAction.invariantsFunctor.map (T.map τ) (β x)) =
        DiscreteAbelianAction.invariantsFunctor.map μ
          (DiscreteAbelianAction.invariantsFunctor.map ε (β x)) :=
    ConcreteCategory.congr_hom hi (β x)
  change DiscreteAbelianAction.trivialInvariantsEquiv G coefficients
    (DiscreteAbelianAction.invariantsFunctor.map ε (β ((H₀.map (T.map τ)) x))) =
      double (DiscreteAbelianAction.trivialInvariantsEquiv G coefficients
        (DiscreteAbelianAction.invariantsFunctor.map ε (β x)))
  rw [hβ]
  exact (congrArg (DiscreteAbelianAction.trivialInvariantsEquiv G coefficients) hix).trans
    (DiscreteAbelianAction.trivialInvariantsEquiv_naturality G doubleCoefficient _)

private lemma mapped_source_coordinate (n : ℤ) :
    nativeCoordinate (comparison (((Γ.rightDerived 0).map τ) (sourceClass n))) =
      ULift.up (n + n) := by
  have h := ConcreteCategory.congr_hom
    (fieldDerivedSectionsContinuousCohomologyIso_naturality.{0, 1} K K 0 τ) (sourceClass n)
  change comparison (((Γ.rightDerived 0).map τ) (sourceClass n)) =
    (H₀.map (T.map τ)) (nativeClass n) at h
  exact (congrArg nativeCoordinate h).trans
    ((nativeCoordinate_map (nativeClass n)).trans
      (congrArg double (nativeClass_coordinate n)))

example : (ULift.up (1 : ℤ) : Coeff) ≠ 0 := by decide

example : DiscreteAbelianAction.homToAdd μ (ULift.up (1 : ℤ)) =
    (ULift.up (2 : ℤ) : Coeff) := rfl

example : μ ≠ 𝟙 M := by
  intro h
  have hx := congrArg
    (fun f : M ⟶ M => DiscreteAbelianAction.homToAdd f (ULift.up (1 : ℤ))) h
  change (ULift.up (2 : ℤ) : Coeff) = ULift.up (1 : ℤ) at hx
  exact (by decide : (2 : ℤ) ≠ 1) (congrArg ULift.down hx)

example : sectionCoordinate (constantSection 1) = ULift.up (1 : ℤ) :=
  constantSection_coordinate 1

example : nativeCoordinate (nativeClass 1) = ULift.up (1 : ℤ) :=
  nativeClass_coordinate 1

example : nativeClass 1 ≠ 0 := by
  intro h
  have hc := congrArg nativeCoordinate h
  rw [nativeClass_coordinate, map_zero] at hc
  exact (by decide : (ULift.up (1 : ℤ) : Coeff) ≠ 0) hc

example : (Γ.rightDerived 0).map τ ≫ comparison = comparison ≫ H₀.map (T.map τ) :=
  fieldDerivedSectionsContinuousCohomologyIso_naturality.{0, 1} K K 0 τ

example : nativeCoordinate (comparison (((Γ.rightDerived 0).map τ) (sourceClass 1))) =
    ULift.up (2 : ℤ) := mapped_source_coordinate 1

example : nativeCoordinate ((H₀.map (T.map τ)) (nativeClass 1)) = ULift.up (2 : ℤ) := by
  exact (nativeCoordinate_map (nativeClass 1)).trans
    (congrArg double (nativeClass_coordinate 1))

example : comparison (((Γ.rightDerived 0).map τ) (sourceClass 1)) ≠ 0 := by
  intro h
  have hc := congrArg nativeCoordinate h
  rw [mapped_source_coordinate, map_zero] at hc
  exact (by decide : (ULift.up (2 : ℤ) : Coeff) ≠ 0) hc

example : comparison (((Γ.rightDerived 0).map τ) (sourceClass 1)) ≠ nativeClass 1 := by
  intro h
  have hc := congrArg nativeCoordinate h
  rw [mapped_source_coordinate, nativeClass_coordinate] at hc
  exact (by decide : (2 : ℤ) ≠ 1) (congrArg ULift.down hc)

end MathlibExtTest.AlgebraicGeometry.Sites.FieldSiteNonzero

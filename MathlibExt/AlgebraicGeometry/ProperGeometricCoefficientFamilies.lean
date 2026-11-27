/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GeometricPerfectTestModels
public import MathlibExt.AlgebraicGeometry.DerivedOrdinaryComplexModels

/-!
# Actual ordinary coefficient families of a fixed proper geometric source

Every algebra A is tested by the actual map Spec A to the fixed ordinary
base test. Algebra arrows give the literal contravariant Spec maps over
that base. The native X_A source is the original fixed fibre sheaf and
its original etale-quotient presentation; its maps are the original
fibre-product maps through those fixed identifications.

References: Toen--Vaquie math/0503269v5, Sections3.1/3.5; Stacks 0DLD,
0DLE and the native source families at AxiomMath/Stacks
c496df0d9beea9deaeabcea8492605f9a0a2313b. This defines the coefficient
and geometric source domains before any DG-moduli comparison.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ProperGeometricCoefficientFamilies

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.EtaleSpacePresentations
open MathlibExt.AlgebraicGeometry.AlgebraicSpaceComplexSourceSites
open MathlibExt.AlgebraicGeometry.ProperSpaceComplexFamilies
open MathlibExt.AlgebraicGeometry.GeometricPerfectTestModels
open MathlibExt.AlgebraicGeometry.DerivedOrdinaryComplexModels

universe u

variable (D : ProperSpaceSituation.{u}) (B : AffineProperFamily D)

/-- The actual scalar ring map from the fixed base coefficient ring. -/
def coefficientRingMap (A : CommAlgCat.{u} B.ring) : B.ring ⟶ ordinaryRing A :=
  CommRingCat.ofHom (algebraMap B.ring A)

/-- Each coefficient algebra gives an actual ordinary scheme map to the original base test. -/
def coefficientBaseMap (A : CommAlgCat.{u} B.ring) : Spec (ordinaryRing A) ⟶ B.test.scheme :=
  Spec.map (coefficientRingMap D B A) ≫ eqToHom B.scheme_eq.symm

/-- The actual algebra arrow, with only its ring structure forgotten. -/
def coefficientRingArrow {A A' : CommAlgCat.{u} B.ring} (f : A ⟶ A') :
    ordinaryRing A ⟶ ordinaryRing A' :=
  CommRingCat.ofHom f.hom.toRingHom

/-- The original algebra map commutes with both coefficient units. -/
theorem coefficientRingMap_comp {A A' : CommAlgCat.{u} B.ring} (f : A ⟶ A') :
    coefficientRingMap D B A ≫ coefficientRingArrow D B f = coefficientRingMap D B A' := by
  ext r
  exact f.hom.commutes r

/-- Spec transport is the native contravariant functor on these same ring maps. -/
theorem coefficientBaseMap_naturality {A A' : CommAlgCat.{u} B.ring} (f : A ⟶ A') :
    Spec.map (coefficientRingArrow D B f) ≫ coefficientBaseMap D B A =
      coefficientBaseMap D B A' := by
  have h : Spec.map (coefficientRingArrow D B f) ≫ Spec.map (coefficientRingMap D B A) =
      Spec.map (coefficientRingMap D B A') := by
    change Scheme.Spec.map (coefficientRingArrow D B f).op ≫
      Scheme.Spec.map (coefficientRingMap D B A).op = Scheme.Spec.map (coefficientRingMap D B A').op
    rw [← Functor.map_comp, ← op_comp, coefficientRingMap_comp]
  rw [coefficientBaseMap, ← Category.assoc, h]
  rfl

/-- The coefficient family is the same original X times_Y Spec A source, with its fixed map to Y. -/
def coefficientFamily (A : CommAlgCat.{u} B.ring) : AffineProperFamily D where
  test :=
    { scheme := Spec (ordinaryRing A)
      map := represented.map (coefficientBaseMap D B A) ≫ B.test.map }
  ring := ordinaryRing A
  scheme_eq := rfl

/-- The actual source arrow to the fixed base is the same Spec algebra map. -/
def coefficientToBase (A : CommAlgCat.{u} B.ring) : (coefficientFamily D B A).test ⟶ B.test :=
  ⟨coefficientBaseMap D B A, rfl⟩

/-- Every coefficient change is the actual Spec arrow over the original fixed target source. -/
def coefficientArrow {A A' : CommAlgCat.{u} B.ring} (f : A ⟶ A') :
    (coefficientFamily D B A').test ⟶ (coefficientFamily D B A).test :=
  ⟨Spec.map (coefficientRingArrow D B f), by
    change represented.map (Spec.map (coefficientRingArrow D B f)) ≫
      (represented.map (coefficientBaseMap D B A) ≫ B.test.map) =
        represented.map (coefficientBaseMap D B A') ≫ B.test.map
    rw [← Category.assoc, ← Functor.map_comp, coefficientBaseMap_naturality]⟩

/-- The native coefficient family space is the original fixed geometric fibre product. -/
abbrev coefficientSpace (A : CommAlgCat.{u} B.ring) :=
  familySpace D (coefficientFamily D B A).test

/-- Its projection to the original X-base family is the literal native fibre-product map. -/
def coefficientSourceMap (A : CommAlgCat.{u} B.ring) :
    coefficientSpace D B A ⟶ familySpace D B.test :=
  familyMap (coefficientToBase D B A)

/-- The coefficient projection still uses the original X_A to Spec A map, without a replacement carrier. -/
def coefficientProjection (A : CommAlgCat.{u} B.ring) :
    (coefficientSpace D B A).sheaf ⟶ represented.obj (Spec (ordinaryRing A)) :=
  affineProperProjection D (coefficientFamily D B A)

/-- The k-projection is the actual A-projection followed by the original Spec coefficient map. -/
def baseCoefficientProjection (A : CommAlgCat.{u} B.ring) :
    (coefficientSpace D B A).sheaf ⟶ represented.obj (Spec B.ring) :=
  coefficientProjection D B A ≫ represented.map (Spec.map (coefficientRingMap D B A))

/-- The native X_f arrow is exactly the original familyMap of this same coefficient arrow. -/
def coefficientGeometricArrow {A A' : CommAlgCat.{u} B.ring} (f : A ⟶ A') :
    coefficientSpace D B A' ⟶ coefficientSpace D B A :=
  familyMap (coefficientArrow D B f)

/-- The original family arrow retains its literal source projection after the fixed fibre identifications. -/
theorem familyMap_projection {T T' : MathlibExt.AlgebraicGeometry.ProperSpaceComplexFamilies.FamilyTest D}
    (h : T ⟶ T') :
    sheafMap (familyMap h) ≫ familyProjection D T' =
      familyProjection D T ≫ represented.map h.schemeMap := by
  simp [sheafMap, familyMap, familyProjection, Category.assoc]

/-- The structural k-projection is the actual native source projection followed by the same coefficient unit. -/
theorem coefficientSourceMap_projection (A : CommAlgCat.{u} B.ring) :
    sheafMap (coefficientSourceMap D B A) ≫ affineProperProjection D B =
      baseCoefficientProjection D B A := by
  rw [coefficientSourceMap, affineProperProjection, ← Category.assoc, familyMap_projection]
  have he : eqToHom B.scheme_eq.symm ≫ eqToHom B.scheme_eq = 𝟙 (Spec B.ring) := by simp
  have hi : represented.map (eqToHom B.scheme_eq.symm) ≫
      represented.map (eqToHom B.scheme_eq) = 𝟙 (represented.obj (Spec B.ring)) :=
    (represented.map_comp _ _).symm.trans
      ((congrArg (fun q => represented.map q) he).trans (represented.map_id _))
  simp only [baseCoefficientProjection, coefficientProjection, affineProperProjection,
    coefficientToBase, coefficientBaseMap, Functor.map_comp, Category.assoc]
  change familyProjection D (coefficientFamily D B A).test ≫
      represented.map (Spec.map (coefficientRingMap D B A)) ≫
        represented.map (eqToHom B.scheme_eq.symm) ≫ represented.map (eqToHom B.scheme_eq) =
    familyProjection D (coefficientFamily D B A).test ≫ represented.map (Spec.map (coefficientRingMap D B A))
  simp only [Category.assoc, hi, Category.comp_id]

end MathlibExt.AlgebraicGeometry.ProperGeometricCoefficientFamilies

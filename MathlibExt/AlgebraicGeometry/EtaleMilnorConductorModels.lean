/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.EtaleCurveTraitModels
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-!
# Whole Milnor triangles and native geometric conductors

The base evaluation cone is formed in sheaves on the native strict local
curve. Its algebraic-closure stalk is compared to the H03 Milnor cone by
an isomorphism of entire triangles. The first comparison is prescribed by
the constant-section unit and the closed-stalk restriction; the second
is the native derived base-change mate and global-section comparison.
Both cone maps and the connecting map are retained by the triangle
isomorphism.

The Galois operator on the Milnor cone is conjugation of the actual
spectrum-induced operator on that base-field stalk. Reduction is the
same native derived extension along the residue map. Thus an arbitrary
post-stalk cone does not receive an independently chosen Galois action.
The rational total dimension is the existing alternating rank-plus-Swan
sum on those exact operators. All source constructions, independence and
integrality remain Wanted requests in the companion module.

Reference: Saito, arXiv:1510.03018v4, Section 1.1, formulas (1.8), (1.15),
and Section 1.3, formulas (1.26)--(1.27); finite local coefficient reduction
on printed page 13 and in the proof of Theorem 4.9. Native mapping cones
and derived base-change reuse Mathlib and the source-normalized Atlas
adapters, with the notices retained in their imported modules.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.EtaleMilnorConductorModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open AdicDerivedContracts CotangentBundleTestModels EtaleStrictLocalizationModels
open EtaleLocalAcyclicityModels EtaleConstantDerivedModels EtaleCurveTraitModels
open _root_.MathlibExt.RingTheory.DerivedModuleScalarOperations

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [CommRing Λ] [DerivedFunctorTheory Λ]

def cochainCone {X Y : Scheme.{0}} {f : X ⟶ Y} {F : Derived Λ X}
    [DerivedConstantAdjunction Λ X] [DerivedConstantAdjunction Λ Y]
    (V : BaseVanishingModel Λ f F) : Cochains Λ Y :=
  ⟨CochainComplex.mappingCone V.arrow.hom, V.boundedCone⟩

/-- The native entire cochain cone triangle, including its connecting sign. -/
def baseCochainTriangle {X Y : Scheme.{0}} {f : X ⟶ Y} {F : Derived Λ X}
    [DerivedConstantAdjunction Λ X] [DerivedConstantAdjunction Λ Y]
    (V : BaseVanishingModel Λ f F) : Pretriangulated.Triangle (Cochains Λ Y) :=
  let cone := cochainCone Λ V
  let connecting : cone.obj ⟶ V.source.obj⟦(1 : ℤ)⟧ :=
    (CochainComplex.mappingCone.triangle V.arrow.hom).mor₃
  Pretriangulated.Triangle.mk V.arrow
    (ObjectProperty.homMk (CochainComplex.mappingCone.inr V.arrow.hom) : V.target ⟶ cone)
    ((CochainComplex.Plus.fullyFaithfulι (ModuleSheaf Λ Y)).preimage
      (connecting ≫
        ((CochainComplex.Plus.ι (ModuleSheaf Λ Y)).commShiftIso (1 : ℤ)).inv.app V.source))

def baseTriangle {X Y : Scheme.{0}} {f : X ⟶ Y} {F : Derived Λ X}
    [DerivedConstantAdjunction Λ X] [DerivedConstantAdjunction Λ Y]
    (V : BaseVanishingModel Λ f F) : Pretriangulated.Triangle (Derived Λ Y) :=
  DerivedCategory.Plus.Q.mapTriangle.obj (baseCochainTriangle Λ V)

def stalkFunctor {Y : Scheme.{0}} (Ω : GeometricField) (t : Spec (.of Ω.carrier) ⟶ Y) :
    Derived Λ Y ⥤ DerivedCategory (ModuleCat.{1} Λ) :=
  derivedPullback Λ t ⋙ derivedSections Λ (Spec (.of Ω.carrier)) ⋙ DerivedCategory.Plus.ι

instance stalkFunctor_commShift {Y : Scheme.{0}} (Ω : GeometricField)
    (t : Spec (.of Ω.carrier) ⟶ Y) : (stalkFunctor Λ Ω t).CommShift ℤ := by
  dsimp only [stalkFunctor, derivedPullback, derivedSections]
  infer_instance

variable {X Y : Scheme.{0}} (Ω : GeometricField) (x : Spec (.of Ω.carrier) ⟶ X)
  (F : Derived Λ X) (f : X ⟶ Y)
  (LX : StrictLocalization Ω x) (LY : StrictLocalization Ω (x ≫ f))
  (M : LocalMorphism Ω x f LX LY) [Trait Ω (x ≫ f) LY]

abbrev localCoefficient : Derived Λ LX.scheme := (derivedPullback Λ LX.map).obj F
abbrev genericField := EtaleCurveTraitModels.genericField Ω (x ≫ f) LY
abbrev geometricGeneric : Generization Ω x f LY := genericGenerization Ω x f LY

variable [DerivedConstantAdjunction Λ LX.scheme] [DerivedConstantAdjunction Λ LY.scheme]
  [DerivedConstantAdjunction Λ (Spec (.of (geometricGeneric Ω x f LY).field.carrier))]

def constantStalkUnit :
    (derivedSections Λ LX.scheme).obj (localCoefficient Λ Ω x F LX) ⟶
      geometricStalk Λ (geometricGeneric Ω x f LY).field (geometricGeneric Ω x f LY).point
        ((derivedConstant Λ LY.scheme).obj
          ((derivedSections Λ LX.scheme).obj (localCoefficient Λ Ω x F LX))) :=
  (DerivedConstantAdjunction.adjunction
    (Λ := Λ) (X := Spec (.of (geometricGeneric Ω x f LY).field.carrier))).unit.app _ ≫
    (derivedSections Λ (Spec (.of (geometricGeneric Ω x f LY).field.carrier))).map
      ((constantPullbackIso Λ (geometricGeneric Ω x f LY).point).inv.app _)

/-- The actual base-change/global-section arrow to the literal Milnor fibre. -/
def nearbyStalkArrow :
    geometricStalk Λ (geometricGeneric Ω x f LY).field (geometricGeneric Ω x f LY).point
      ((derivedPushforward Λ M.map).obj (localCoefficient Λ Ω x F LX)) ⟶
        milnorSections Λ Ω x F f LX LY M (geometricGeneric Ω x f LY) :=
  (derivedSections Λ (Spec (.of (geometricGeneric Ω x f LY).field.carrier))).map
      (baseChangeMap Λ (milnorProjection Ω x f LX LY M (geometricGeneric Ω x f LY))
        (pullback.snd M.map (geometricGeneric Ω x f LY).point) M.map
        (geometricGeneric Ω x f LY).point pullback.condition (localCoefficient Λ Ω x F LX)) ≫
    (GlobalSectionsPushforward.comparison
      (R := Λ) (f := pullback.snd M.map (geometricGeneric Ω x f LY).point)).hom.app _

variable (V : BaseVanishingModel Λ M.map (localCoefficient Λ Ω x F LX))
  [IsIso (closedStalkArrow Λ Ω x LX F)]
  [IsIso (constantStalkUnit Λ Ω x F f LX LY)]
  (W : VanishingModel Λ Ω x F f LX LY M (geometricGeneric Ω x f LY))

def genericTriangle : Pretriangulated.Triangle (DerivedCategory (ModuleCat.{1} Λ)) :=
  (stalkFunctor Λ (geometricGeneric Ω x f LY).field
    (geometricGeneric Ω x f LY).point).mapTriangle.obj
    (baseTriangle Λ V)

def milnorTriangle : Pretriangulated.Triangle (DerivedCategory (ModuleCat.{1} Λ)) :=
  DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle W.arrow)

def sourceComparison : (genericTriangle Λ Ω x F f LX LY M V).obj₁ ⟶
    (milnorTriangle Λ Ω x F f LX LY M W).obj₁ :=
  (stalkFunctor Λ (geometricGeneric Ω x f LY).field (geometricGeneric Ω x f LY).point).map
      V.sourceIso.hom ≫
    (inv (constantStalkUnit Λ Ω x F f LX LY)).hom ≫
      (closedStalkArrow Λ Ω x LX F).hom ≫ W.sourceIso.inv

def targetComparison : (genericTriangle Λ Ω x F f LX LY M V).obj₂ ⟶
    (milnorTriangle Λ Ω x F f LX LY M W).obj₂ :=
  (stalkFunctor Λ (geometricGeneric Ω x f LY).field (geometricGeneric Ω x f LY).point).map
      V.targetIso.hom ≫
    (nearbyStalkArrow Λ Ω x F f LX LY M).hom ≫ W.targetIso.inv

/-- Every arrow of the triangle is compared; the first two maps are fixed
by the actual restriction and base-change arrows. -/
structure MilnorComparison where
  comparison : genericTriangle Λ Ω x F f LX LY M V ≅ milnorTriangle Λ Ω x F f LX LY M W
  source : comparison.hom.hom₁ = sourceComparison Λ Ω x F f LX LY M V W
  target : comparison.hom.hom₂ = targetComparison Λ Ω x F f LX LY M V W

def genericVanishing : Derived Λ (Spec (.of (genericField Ω x f LY))) :=
  BaseVanishingModel.generic Λ V (genericField Ω x f LY) (genericMap Ω (x ≫ f) LY)

/-- The field-sheaf stalk and the whole base-cone stalk are identified by
the same normalized native pullback composition map. -/
def fieldConeIso :
    (EtaleGaloisStalkActions.fieldStalk Λ (genericField Ω x f LY)
      (genericVanishing Λ Ω x F f LX LY M V)).obj ≅
        (genericTriangle Λ Ω x F f LX LY M V).obj₃ := by
  change ((derivedSections Λ (Spec (.of (AlgebraicClosure (genericField Ω x f LY))))).obj
    ((derivedPullback Λ (EtaleGaloisStalkActions.closurePoint (genericField Ω x f LY))).obj
      ((derivedPullback Λ (genericMap Ω (x ≫ f) LY)).obj V.object))).obj ≅
    ((derivedSections Λ (Spec (.of (AlgebraicClosure (genericField Ω x f LY))))).obj
      ((derivedPullback Λ (EtaleGaloisStalkActions.closurePoint (genericField Ω x f LY) ≫
        genericMap Ω (x ≫ f) LY)).obj V.object)).obj
  exact DerivedCategory.Plus.ι.mapIso
    ((derivedSections Λ (Spec (.of (AlgebraicClosure (genericField Ω x f LY))))).mapIso
      ((DerivedPullbackPasting.comparison
        (R := Λ) (f := EtaleGaloisStalkActions.closurePoint (genericField Ω x f LY))
        (g := genericMap Ω (x ≫ f) LY)).app V.object))

variable (A : MilnorComparison Λ Ω x F f LX LY M V W)

def MilnorComparison.coneIso :
    (EtaleGaloisStalkActions.fieldStalk Λ (genericField Ω x f LY)
      (genericVanishing Λ Ω x F f LX LY M V)).obj ≅ W.object :=
  fieldConeIso Λ Ω x F f LX LY M V ≪≫ asIso A.comparison.hom.hom₃

/-- Galois on the Milnor cone is transported from the fixed base sheaf;
there is no independent representation parameter on that cone. -/
def MilnorComparison.operator (g : Field.absoluteGaloisGroup (genericField Ω x f LY)) :
    W.object ⟶ W.object :=
  (A.coneIso Λ Ω x F f LX LY M V W).inv ≫
    (EtaleGaloisStalkActions.deckOperator Λ (genericField Ω x f LY)
      (genericVanishing Λ Ω x F f LX LY M V) g).hom ≫
        (A.coneIso Λ Ω x F f LX LY M V W).hom

theorem MilnorComparison.operator_intertwines
    (g : Field.absoluteGaloisGroup (genericField Ω x f LY)) :
    (EtaleGaloisStalkActions.deckOperator Λ (genericField Ω x f LY)
      (genericVanishing Λ Ω x F f LX LY M V) g).hom ≫
        (A.coneIso Λ Ω x F f LX LY M V W).hom =
    (A.coneIso Λ Ω x F f LX LY M V W).hom ≫ A.operator Λ Ω x F f LX LY M V W g := by
  simp only [MilnorComparison.operator, Iso.hom_inv_id_assoc]

def MilnorComparison.reducedConeIso [IsLocalRing Λ] [HasExtension (IsLocalRing.residue Λ)] :
    (extension (IsLocalRing.residue Λ)).obj
      (EtaleGaloisStalkActions.fieldStalk Λ (genericField Ω x f LY)
        (genericVanishing Λ Ω x F f LX LY M V)).obj ≅
    (extension (IsLocalRing.residue Λ)).obj W.object :=
  (extension (IsLocalRing.residue Λ)).mapIso (A.coneIso Λ Ω x F f LX LY M V W)

/-- The coefficient change is applied to that same actual cone operator. -/
def MilnorComparison.reducedOperator [IsLocalRing Λ] [HasExtension (IsLocalRing.residue Λ)]
    (g : Field.absoluteGaloisGroup (genericField Ω x f LY)) :
    (extension (IsLocalRing.residue Λ)).obj W.object ⟶
      (extension (IsLocalRing.residue Λ)).obj W.object :=
  (extension (IsLocalRing.residue Λ)).map (A.operator Λ Ω x F f LX LY M V W g)

theorem MilnorComparison.reduction_intertwines [IsLocalRing Λ]
    [HasExtension (IsLocalRing.residue Λ)]
    (g : Field.absoluteGaloisGroup (genericField Ω x f LY)) :
    (extension (IsLocalRing.residue Λ)).map
      (EtaleGaloisStalkActions.deckOperator Λ (genericField Ω x f LY)
        (genericVanishing Λ Ω x F f LX LY M V) g).hom ≫
      (A.reducedConeIso Λ Ω x F f LX LY M V W).hom =
    (A.reducedConeIso Λ Ω x F f LX LY M V W).hom ≫
      A.reducedOperator Λ Ω x F f LX LY M V W g := by
  simpa only [MilnorComparison.reducedConeIso, MilnorComparison.reducedOperator,
    Functor.mapIso_hom, Functor.map_comp] using
      congrArg ((extension (IsLocalRing.residue Λ)).map)
        (A.operator_intertwines Λ Ω x F f LX LY M V W g)

def totalDimension [Finite Λ] [IsLocalRing Λ]
    [HasExtension (IsLocalRing.residue Λ)]
    (B : FiniteRamificationStalkModels.BoundedRamification (genericField Ω x f LY) Λ
      (IsLocalRing.ResidueField Λ) (IsLocalRing.residue Λ) (localRing Ω (x ≫ f) LY)
      (genericVanishing Λ Ω x F f LX LY M V)) : ℚ :=
  FiniteRamificationStalkModels.totalDimension _ _ _ _ _ _ B

end MathlibExt.AlgebraicGeometry.EtaleMilnorConductorModels

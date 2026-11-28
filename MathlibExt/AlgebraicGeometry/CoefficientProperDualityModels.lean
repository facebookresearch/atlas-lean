/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CoefficientCompactSupportModels
public import Mathlib.CategoryTheory.Shift.Adjunction

/-!
# Proper coefficient traces from the actual compact-support duality

This coefficient-field adapter reuses the completed construction in
`ProperBettiFunctoriality`: compact sections pull back by the native
inverse-image unit; all bounded-below derived maps are normalized by
the native derived units. Borel--Moore pushforward is precomposition
under the two actual compact-support dualizing representations.
There is no separately supplied cohomological trace operator.

Reference: Kashiwara--Schapira, Sheaves on Manifolds, Sections2.5--3.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.CoefficientProperDualityModels
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.Opposite
open ConstructibleComplexes CoefficientBettiModels CoefficientCompactSupportModels
attribute [local instance] HasDerivedCategory.standard
variable (k : Type) [Field k]

/-- The homology carrier is native derived Hom into the represented dualizing object. -/
abbrev BorelMoore (Z : TopCat.{0}) (D : DualizingComplex k Z) (n : ℤ) : Type 1 :=
  coefficientUnit k Z ⟶ D.obj⟦-n⟧

/-- Actual derived inverse image on bounded-below rational complexes. -/
abbrev inverseImagePlus {Z W : TopCat.{0}} (f : Z ⟶ W) :=
  (pullback k f).rightDerivedFunctorPlus
/-- Actual derived compact-support section functor with bounded-below target. -/
abbrev compactDerived (Z : TopCat.{0}) := (sections k Z).rightDerivedFunctorPlus

/-- Compact support of the fixed section map, not a choice of map. -/
structure SectionSupport {Z W : TopCat.{0}} (f : Z ⟶ W) : Prop where
  compact : ∀ (F : CoefficientSheaf k W) (s : compactSections k F),
    IsCompact (closure (germSupport k ((pullback k f).obj F)
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f).unit.app F).hom.app
        (op ⊤) s.1)))

/-- Pullback of a compact section is the actual adjunction-unit section. -/
def sectionPullback {Z W : TopCat.{0}} (f : Z ⟶ W) (P : SectionSupport k f)
    (F : CoefficientSheaf k W) :
    compactSections k F →ₗ[k] compactSections k ((pullback k f).obj F) where
  toFun s := ⟨((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f).unit.app F).hom.app
    (op ⊤) s.1, P.compact F s⟩
  map_add' s t := by ext; exact map_add _ _ _
  map_smul' r s := by ext; exact map_smul _ _ _

/-- Naturality follows from the actual sheaf inverse-image unit. -/
def sectionPullbackNat {Z W : TopCat.{0}} (f : Z ⟶ W) (P : SectionSupport k f) :
    sections k W ⟶ pullback k f ⋙ sections k Z where
  app F := ModuleCat.ofHom (sectionPullback k f P F)
  naturality {F G} a := by
    ext s
    apply Subtype.ext
    have h := (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f).unit.naturality a
    exact congrArg (fun b => (b.hom.app (op ⊤)).hom s.1) h

/-- Actual compact-support derived Hom into the rational coefficient unit. -/
abbrev CompactDualHom (Z : TopCat.{0}) (n : ℤ) : Type 1 :=
  (derivedSections k Z).obj ((unitPlus k Z)⟦n⟧) ⟶ vectorUnit k

/-- Shift adjunction from Borel--Moore degree to the dualizing representation. -/
def bmAdjoint (Z : TopCat.{0}) (D : DualizingComplex k Z) (n : ℤ) :
    BorelMoore k Z D n →ₗ[k] (DerivedCategory.Plus.ι.obj ((unitPlus k Z)⟦n⟧) ⟶ D.obj) where
  toFun a := (DerivedCategory.Plus.ι.commShiftIso n).hom.app (unitPlus k Z) ≫
    (shiftFunctor (CoefficientDerived k Z) n).map a ≫
      (shiftFunctorCompIsoId (CoefficientDerived k Z) (-n) n (neg_add_cancel n)).hom.app D.obj
  map_add' a b := by
    simp [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' r a := by
    simp [Functor.map_smul, Linear.smul_comp, Linear.comp_smul]

/-- The shift-adjunction map is a rational linear equivalence. -/
def bmAdjointEquiv (Z : TopCat.{0}) (D : DualizingComplex k Z) (n : ℤ) :
    BorelMoore k Z D n ≃ₗ[k] (DerivedCategory.Plus.ι.obj ((unitPlus k Z)⟦n⟧) ⟶ D.obj) :=
  LinearEquiv.ofBijective (bmAdjoint k Z D n) (by
    let A := (DerivedCategory.Plus.ι.commShiftIso n).app (unitPlus k Z)
    let a := (shiftEquiv (CoefficientDerived k Z) n).toAdjunction.homEquiv (coefficientUnit k Z)
      D.obj
    change Function.Bijective ((fun f => A.hom ≫ f) ∘ a.symm)
    apply Function.Bijective.comp _ a.symm.bijective
    constructor
    · intro a b h
      exact (cancel_epi A.hom).mp h
    · intro b
      exact ⟨A.inv ≫ b, by simp⟩)

/-- The actual dualizing representation gives the compact-support Hom equivalence. -/
def bmDualHomEquiv (Z : TopCat.{0}) (D : DualizingComplex k Z) (n : ℤ) :
    BorelMoore k Z D n ≃ₗ[k] CompactDualHom k Z n :=
  (bmAdjointEquiv k Z D n).trans
    (D.representation.app (op ((unitPlus k Z)⟦n⟧))).toLinearEquiv

def unitComplex (Z : TopCat.{0}) : CochainComplex.Plus (CoefficientSheaf k Z) :=
  ⟨(CochainComplex.singleFunctor (CoefficientSheaf k Z) 0).obj (((constant k Z).obj (ModuleCat.of k
    k))),
    ⟨0, inferInstance⟩⟩

/-- The actual cochain constant complex has the fixed bounded-below coefficient image. -/
@[simp] theorem unitComplex_image (Z : TopCat.{0}) :
    DerivedCategory.Plus.Q.obj (unitComplex k Z) = unitPlus k Z := by rfl

def coefficientUnitMap {Z W : TopCat.{0}} (f : Z ⟶ W) :
    unitPlus k Z ⟶ (inverseImagePlus k f).obj (unitPlus k W) := by
  let cochain : unitComplex k Z ⟶ (pullback k f).mapCochainComplexPlus.obj (unitComplex k W) :=
    ObjectProperty.homMk
      ((CochainComplex.singleFunctor (CoefficientSheaf k Z) 0).map
        ((constantPullbackIso k f).app (ModuleCat.of k k)).inv ≫
        (HomologicalComplex.singleMapHomologicalComplex (pullback k f)
          (ComplexShape.up ℤ) 0).inv.app (((constant k W).obj (ModuleCat.of k k))))
  exact DerivedCategory.Plus.Q.map cochain ≫
    (pullback k f).rightDerivedFunctorPlusUnit.app (unitComplex k W)

/-- A derived compact-support pullback fixed by actual cochain maps and units. -/
structure ProperPullback {Z W : TopCat.{0}} (f : Z ⟶ W) where
  support : SectionSupport k f
  unitIso : (inverseImagePlus k f).obj (unitPlus k W) ≅ unitPlus k Z
  unit_normalization : unitIso.inv = coefficientUnitMap k f
  map : compactDerived k W ⟶ inverseImagePlus k f ⋙ compactDerived k Z
  compatibility : ∀ K : CochainComplex.Plus (CoefficientSheaf k W),
    (sections k W).rightDerivedFunctorPlusUnit.app K ≫ map.app (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map ((sectionPullbackNat k f support).mapCochainComplexPlus.app K) ≫
        (sections k Z).rightDerivedFunctorPlusUnit.app ((pullback k f).mapCochainComplexPlus.obj K)
          ≫
        (compactDerived k Z).map ((pullback k f).rightDerivedFunctorPlusUnit.app K)

/-- The fixed compact-support pullback on shifted rational coefficient complexes. -/
def compactPullback {Z W : TopCat.{0}} {f : Z ⟶ W} (P : ProperPullback k f) (n : ℤ) :
    (derivedSections k W).obj ((unitPlus k W)⟦n⟧) ⟶
      (derivedSections k Z).obj ((unitPlus k Z)⟦n⟧) :=
  DerivedCategory.Plus.ι.map (P.map.app ((unitPlus k W)⟦n⟧) ≫
    (compactDerived k Z).map
      (((inverseImagePlus k f).commShiftIso n).hom.app (unitPlus k W) ≫
        (shiftFunctor (DerivedCategory.Plus (CoefficientSheaf k Z)) n).map P.unitIso.hom))

/-- Precomposition on the actual compact-support duals. -/
def compactDualPullback {Z W : TopCat.{0}} {f : Z ⟶ W} (P : ProperPullback k f) (n : ℤ) :
    CompactDualHom k Z n →ₗ[k] CompactDualHom k W n where
  toFun a := compactPullback k P n ≫ a
  map_add' a b := by simp [Preadditive.comp_add]
  map_smul' r a := by simp [Linear.comp_smul]

/-- Proper Borel--Moore pushforward, constructed from normalized support data. -/
def borelMoorePushforward {Z W : TopCat.{0}} {f : Z ⟶ W} (P : ProperPullback k f)
    (DX : DualizingComplex k Z) (DY : DualizingComplex k W) (n : ℤ) :
    BorelMoore k Z DX n →ₗ[k] BorelMoore k W DY n :=
  (bmDualHomEquiv k W DY n).symm.toLinearMap ∘ₗ
    compactDualPullback k P n ∘ₗ (bmDualHomEquiv k Z DX n).toLinearMap

/-- A cohomology class caps an actual supported homology class by native shifted composition. -/
def cap (Z : TopCat.{0}) (D : DualizingComplex k Z) (n m : ℤ)
    (c : BorelMoore k Z D m) :
    CoefficientBettiModels.Cohomology k Z n →ₗ[k] BorelMoore k Z D (m-n) where
  toFun a := a ≫ (shiftFunctor (CoefficientDerived k Z) n).map c ≫
    (shiftFunctorAdd' (CoefficientDerived k Z) (-m) n (-(m-n)) (by omega)).inv.app D.obj
  map_add' a b := by simp [Preadditive.add_comp]
  map_smul' r a := by simp [Linear.smul_comp]

/-- The fundamental class is determined by the actual smooth purity. -/
def fundamentalClass (Z : TopCat.{0}) (D : DualizingComplex k Z) (d : ℕ)
    (e : D.obj ≅ (coefficientUnit k Z)⟦(2 * d : ℤ)⟧) : BorelMoore k Z D (2*d) :=
  (shiftFunctorZero (CoefficientDerived k Z) ℤ).inv.app (coefficientUnit k Z) ≫
    (shiftFunctorAdd' (CoefficientDerived k Z) (2*d : ℤ) (-(2*d : ℤ)) 0
      (add_neg_cancel _)).hom.app (coefficientUnit k Z) ≫
    (shiftFunctor (CoefficientDerived k Z) (-(2*d : ℤ))).map e.inv

/-- Poincare identification is a native linear equivalence of derived Hom groups. -/
def purityCohomologyEquiv (Z : TopCat.{0}) (D : DualizingComplex k Z) (d : ℕ)
    (e : D.obj ≅ (coefficientUnit k Z)⟦(2 * d : ℤ)⟧) (n : ℤ) :
    BorelMoore k Z D ((2*d : ℤ)-n) ≃ₗ[k] CoefficientBettiModels.Cohomology k Z n := by
  let a : D.obj⟦-((2*d : ℤ)-n)⟧ ≅ (coefficientUnit k Z)⟦n⟧ :=
    (shiftFunctor (CoefficientDerived k Z) (-((2*d : ℤ)-n))).mapIso e ≪≫
      (shiftFunctorAdd' (CoefficientDerived k Z) (2*d : ℤ) (-((2*d : ℤ)-n)) n
        (by omega)).symm.app (coefficientUnit k Z)
  exact {
    toFun := fun x => x ≫ a.hom
    invFun := fun x => x ≫ a.inv
    left_inv := by intro x; simp
    right_inv := by intro x; simp
    map_add' := by intro x y; simp [Preadditive.add_comp]
    map_smul' := by intro r x; simp [Linear.smul_comp] }

/-- The homology-indexed identification keeps the exact trace degree without implicit casts. -/
def purityHomologyEquiv (Z : TopCat.{0}) (D : DualizingComplex k Z) (d : ℕ)
    (e : D.obj ≅ (coefficientUnit k Z)⟦(2 * d : ℤ)⟧) (m : ℤ) :
    BorelMoore k Z D m ≃ₗ[k] CoefficientBettiModels.Cohomology k Z ((2*d : ℤ)-m) := by
  let a : D.obj⟦-m⟧ ≅ (coefficientUnit k Z)⟦(2*d : ℤ)-m⟧ :=
    (shiftFunctor (CoefficientDerived k Z) (-m)).mapIso e ≪≫
      (shiftFunctorAdd' (CoefficientDerived k Z) (2*d : ℤ) (-m) ((2*d : ℤ)-m)
        (by omega)).symm.app (coefficientUnit k Z)
  exact {
    toFun := fun x => x ≫ a.hom
    invFun := fun x => x ≫ a.inv
    left_inv := by intro x; simp
    right_inv := by intro x; simp
    map_add' := by intro x y; simp [Preadditive.add_comp]
    map_smul' := by intro r x; simp [Linear.smul_comp] }

/-- Proper trace on a supported class uses its actual projection and the target purity. -/
def supportedTrace {R X Z : TopCat.{0}} (p : R ⟶ X) (q : R ⟶ Z)
    (P : ProperPullback k p) (DR : DualizingComplex k R) (DX : DualizingComplex k X)
    (dX : ℕ) (eX : DX.obj ≅ (coefficientUnit k X)⟦(2 * dX : ℤ)⟧)
    (m n : ℤ) (c : BorelMoore k R DR m) :
    CoefficientBettiModels.Cohomology k Z n →ₗ[k]
      CoefficientBettiModels.Cohomology k X ((2*dX : ℤ)-(m-n)) :=
  (purityHomologyEquiv k X DX dX eX (m-n)).toLinearMap ∘ₗ
    borelMoorePushforward k P DR DX (m-n) ∘ₗ
      cap k R DR n m c ∘ₗ CoefficientBettiModels.cohomologyPullback k q n

/-- A shift identity behind the fundamental class: shifting back the purity-defined class
recovers the inverse purity. -/
theorem shift_fundamentalClass_aux {C : Type*} [Category C] [HasShift C ℤ] (U V : C) (n : ℤ)
    (e : V ≅ U⟦n⟧) :
    ((shiftFunctorZero C ℤ).inv.app U ≫
        (shiftFunctorAdd' C n (-n) 0 (add_neg_cancel n)).hom.app U ≫ e.inv⟦-n⟧')⟦n⟧' ≫
      (shiftFunctorCompIsoId C (-n) n (neg_add_cancel n)).hom.app V = e.inv := by
  have h1 : (shiftFunctorZero C ℤ).inv.app U ≫
      (shiftFunctorAdd' C n (-n) 0 (add_neg_cancel n)).hom.app U =
      (shiftFunctorCompIsoId C n (-n) (add_neg_cancel n)).inv.app U := by
    simp [shiftFunctorCompIsoId]
  have h2 := (shiftFunctorCompIsoId C (-n) n (neg_add_cancel n)).hom.naturality e.inv
  simp only [Functor.comp_map, Functor.id_map] at h2
  rw [← Category.assoc, Functor.map_comp, h1, shift_shiftFunctorCompIsoId_inv_app,
    Category.assoc, h2, Iso.inv_hom_id_app_assoc]

/-- The shift adjoint of the fundamental class is the inverse purity. -/
theorem bmAdjoint_fundamentalClass (Z : TopCat.{0}) (D : DualizingComplex k Z) (d : ℕ)
    (e : D.obj ≅ (coefficientUnit k Z)⟦(2 * d : ℤ)⟧) :
    bmAdjoint k Z D (2 * d) (fundamentalClass k Z D d e) =
      (DerivedCategory.Plus.ι.commShiftIso (2 * d : ℤ)).hom.app (unitPlus k Z) ≫ e.inv := by
  simp only [bmAdjoint, fundamentalClass, LinearMap.coe_mk, AddHom.coe_mk]
  congr 1
  exact shift_fundamentalClass_aux _ _ _ e

/-- The fundamental class corresponds, under the dualizing representation, to the top trace
induced by the same purity. -/
theorem bmDualHomEquiv_fundamentalClass (Z : TopCat.{0}) (D : DualizingComplex k Z) (d : ℕ)
    (e : D.obj ≅ (coefficientUnit k Z)⟦(2 * d : ℤ)⟧) :
    bmDualHomEquiv k Z D (2 * d) (fundamentalClass k Z D d e) = topTrace k Z D d e := by
  change (D.representation.app (Opposite.op ((unitPlus k Z)⟦(2 * d : ℤ)⟧))).toLinearEquiv
    (bmAdjoint k Z D (2 * d) (fundamentalClass k Z D d e)) = _
  rw [bmAdjoint_fundamentalClass]
  rfl

/-- Proper pushforward carries fundamental classes to fundamental classes when the actual compact
pullback carries the one top trace to the other. -/
theorem borelMoorePushforward_fundamentalClass {Z W : TopCat.{0}} {f : Z ⟶ W}
    (P : ProperPullback k f) (DZ : DualizingComplex k Z) (DW : DualizingComplex k W) (d : ℕ)
    (eZ : DZ.obj ≅ (coefficientUnit k Z)⟦(2 * d : ℤ)⟧)
    (eW : DW.obj ≅ (coefficientUnit k W)⟦(2 * d : ℤ)⟧)
    (h : compactPullback k P (2 * d) ≫ topTrace k Z DZ d eZ = topTrace k W DW d eW) :
    borelMoorePushforward k P DZ DW (2 * d) (fundamentalClass k Z DZ d eZ) =
      fundamentalClass k W DW d eW := by
  apply (bmDualHomEquiv k W DW (2 * d)).injective
  simp only [borelMoorePushforward, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.apply_symm_apply, bmDualHomEquiv_fundamentalClass]
  exact h

end MathlibExt.AlgebraicGeometry.CoefficientProperDualityModels

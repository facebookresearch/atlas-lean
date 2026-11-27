/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RootParabolicPeriodModels
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Native tensor and inverse image on actual invertible modules with sections

All objects and arrows lie in the existing DivisorObject groupoid.
Tensor, sections, module maps and arbitrary scheme inverse images are
the native sheaf-module operations. The input certificates are only
line landing and preservation of sections by fixed native coherence
maps. Their constructors are separate from parabolic equivalence.

Source: Borne–Vistoli arXiv:1001.0466v2, Definition3.1.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 400000
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DivisorNativeOperations

open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.CategoryTheory.MonoidalCategory
open _root_.Opposite _root_.AlgebraicGeometry
open DeligneFaltingsCategories LineBundleTaskContracts AlgebraicLineBundleFamilies CoherentCurveLinearSeries
open RootParabolicPeriodModels
open ModuleTensorPullbackSections

structure Landing : Prop where
  tensor_line : ∀ (X : Scheme.{0}) (L M : DivisorObject X),
    IsLineBundle (moduleTensor X L.module M.module)
  pullback_line : ∀ {X Y : Scheme.{0}} (f : Y ⟶ X) (L : DivisorObject X),
    IsLineBundle ((Scheme.Modules.pullback f).obj L.module)
  pullback_unit : ∀ {X Y : Scheme.{0}} (f : Y ⟶ X),
    IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)

variable (H : Landing)

def tensor (X : Scheme.{0}) (L M : DivisorObject X) : DivisorObject X :=
  ⟨moduleTensor X L.module M.module, H.tensor_line X L M,
    (tensorLeftUnit X (structureModule X)).inv ≫ tensorMap L.sectionMap M.sectionMap⟩

def tensorHom {X : Scheme.{0}} {L L' M M' : DivisorObject X}
    (f : L ⟶ L') (g : M ⟶ M') : tensor H X L M ⟶ tensor H X L' M' :=
  ⟨sheafTensorIso f.iso g.iso, by
    change ((tensorLeftUnit X (structureModule X)).inv ≫ tensorMap L.sectionMap M.sectionMap) ≫
      tensorMap f.iso.hom g.iso.hom =
        (tensorLeftUnit X (structureModule X)).inv ≫ tensorMap L'.sectionMap M'.sectionMap
    rw [Category.assoc, ← tensorMap_comp, f.section_eq, g.section_eq]⟩

def tensorFunctor (X : Scheme.{0}) : DivisorObject X × DivisorObject X ⥤ DivisorObject X where
  obj L := tensor H X L.1 L.2
  map f := tensorHom H f.1 f.2
  map_id L := by
    apply DivisorObject.Hom.ext
    apply Iso.ext
    change tensorMap (𝟙 L.1.module) (𝟙 L.2.module) = 𝟙 (moduleTensor X L.1.module L.2.module)
    simp
  map_comp f g := by
    apply DivisorObject.Hom.ext
    apply Iso.ext
    change tensorMap (f.1.iso.hom ≫ g.1.iso.hom) (f.2.iso.hom ≫ g.2.iso.hom) =
      tensorMap f.1.iso.hom f.2.iso.hom ≫ tensorMap g.1.iso.hom g.2.iso.hom
    rw [tensorMap_comp]

def pullback {X Y : Scheme.{0}} (f : Y ⟶ X) (L : DivisorObject X) : DivisorObject Y := by
  letI := H.pullback_unit f
  exact ⟨(Scheme.Modules.pullback f).obj L.module, H.pullback_line f L,
    (asIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)).inv ≫
      (Scheme.Modules.pullback f).map L.sectionMap⟩

def pullbackHom {X Y : Scheme.{0}} (f : Y ⟶ X) {L M : DivisorObject X}
    (a : L ⟶ M) : pullback H f L ⟶ pullback H f M := by
  letI := H.pullback_unit f
  refine ⟨(Scheme.Modules.pullback f).mapIso a.iso, ?_⟩
  change ((asIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)).inv ≫
    (Scheme.Modules.pullback f).map L.sectionMap) ≫ (Scheme.Modules.pullback f).map a.iso.hom =
      (asIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)).inv ≫
        (Scheme.Modules.pullback f).map M.sectionMap
  rw [Category.assoc, ← Functor.map_comp, a.section_eq]

def pullbackFunctor {X Y : Scheme.{0}} (f : Y ⟶ X) : DivisorObject X ⥤ DivisorObject Y where
  obj L := pullback H f L
  map a := pullbackHom H f a
  map_id L := by
    apply DivisorObject.Hom.ext
    apply Iso.ext
    change (Scheme.Modules.pullback f).map (𝟙 L.module) = 𝟙 _
    exact (Scheme.Modules.pullback f).map_id _
  map_comp a b := by
    apply DivisorObject.Hom.ext
    apply Iso.ext
    change (Scheme.Modules.pullback f).map (a.iso.hom ≫ b.iso.hom) =
      (Scheme.Modules.pullback f).map a.iso.hom ≫ (Scheme.Modules.pullback f).map b.iso.hom
    exact (Scheme.Modules.pullback f).map_comp _ _

/-- Proofs only: every coherence map below is already a fixed native module map. -/
structure Coherence : Prop where
  left_unit : ∀ (X : Scheme.{0}) (L : DivisorObject X),
    (tensor H X (DivisorObject.unitObject X) L).sectionMap ≫
      (tensorLeftUnit X L.module).hom = L.sectionMap
  right_unit : ∀ (X : Scheme.{0}) (L : DivisorObject X),
    (tensor H X L (DivisorObject.unitObject X)).sectionMap ≫
      (tensorRightUnit X L.module).hom = L.sectionMap
  symmetry : ∀ (X : Scheme.{0}) (L M : DivisorObject X),
    (tensor H X L M).sectionMap ≫ (tensorSwap X L.module M.module).hom = (tensor H X M L).sectionMap
  tripleLeft_iso : ∀ (X : Scheme.{0}) (L M N : DivisorObject X), IsIso (tripleLeft X L.module M.module N.module)
  tripleRight_iso : ∀ (X : Scheme.{0}) (L M N : DivisorObject X), IsIso (tripleRight X L.module M.module N.module)
  associativity : ∀ (X : Scheme.{0}) (L M N : DivisorObject X),
    letI := tripleLeft_iso X L M N
    (tensor H X (tensor H X L M) N).sectionMap ≫
      (asIso (tripleLeft X L.module M.module N.module)).inv ≫ tripleRight X L.module M.module N.module =
        (tensor H X L (tensor H X M N)).sectionMap
  pullbackTensor : ∀ {X Y : Scheme.{0}} (f : Y ⟶ X) (P : PullbackTensorData f)
      (L M : DivisorObject X),
    (tensor H Y (pullback H f L) (pullback H f M)).sectionMap ≫
      (P.comparison L.module M.module).inv = (pullback H f (tensor H X L M)).sectionMap

variable (C : Coherence H)

def leftUnitor (X : Scheme.{0}) (L : DivisorObject X) : tensor H X (DivisorObject.unitObject X) L ≅ L :=
  asIso (show tensor H X (DivisorObject.unitObject X) L ⟶ L from
    ⟨tensorLeftUnit X L.module, C.left_unit X L⟩)

def rightUnitor (X : Scheme.{0}) (L : DivisorObject X) : tensor H X L (DivisorObject.unitObject X) ≅ L :=
  asIso (show tensor H X L (DivisorObject.unitObject X) ⟶ L from
    ⟨tensorRightUnit X L.module, C.right_unit X L⟩)

def symmetry (X : Scheme.{0}) (L M : DivisorObject X) : tensor H X L M ≅ tensor H X M L :=
  asIso (show tensor H X L M ⟶ tensor H X M L from
    ⟨tensorSwap X L.module M.module, C.symmetry X L M⟩)

def associator (X : Scheme.{0}) (L M N : DivisorObject X) :
    tensor H X (tensor H X L M) N ≅ tensor H X L (tensor H X M N) := by
  letI := C.tripleLeft_iso X L M N
  letI := C.tripleRight_iso X L M N
  exact asIso (show tensor H X (tensor H X L M) N ⟶ tensor H X L (tensor H X M N) from
    ⟨(asIso (tripleLeft X L.module M.module N.module)).symm ≪≫
      asIso (tripleRight X L.module M.module N.module), C.associativity X L M N⟩)

/-- Every computational field of the native monoidal structure is fixed. -/
@[instance_reducible]
def monoidalStruct (X : Scheme.{0}) : MonoidalCategoryStruct (DivisorObject X) where
  tensorObj L M := tensor H X L M
  whiskerLeft L _ _ f := tensorHom H (𝟙 L) f
  whiskerRight f M := tensorHom H f (𝟙 M)
  tensorHom f g := tensorHom H f g
  tensorUnit := DivisorObject.unitObject X
  associator := associator H C X
  leftUnitor := leftUnitor H C X
  rightUnitor := rightUnitor H C X

def pullbackUnit {X Y : Scheme.{0}} (f : Y ⟶ X) :
    DivisorObject.unitObject Y ⟶ pullback H f (DivisorObject.unitObject X) := by
  letI := H.pullback_unit f
  refine ⟨(asIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)).symm, ?_⟩
  change (𝟙 _) ≫ (asIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)).inv =
    (asIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)).inv ≫
      (Scheme.Modules.pullback f).map (𝟙 _)
  simp
  rfl

def pullbackTensor {X Y : Scheme.{0}} (f : Y ⟶ X) (P : PullbackTensorData f)
    (L M : DivisorObject X) :
    tensor H Y (pullback H f L) (pullback H f M) ⟶ pullback H f (tensor H X L M) :=
  ⟨(P.comparison L.module M.module).symm, C.pullbackTensor f P L M⟩

/-- Native symmetric monoidal realization and arbitrary scheme inverse
image, with every structure map equal to its preceding actual recipe. -/
structure Realization where
  monoidal : ∀ X : Scheme.{0}, MonoidalCategory (DivisorObject X)
  data_eq : ∀ X : Scheme.{0}, (monoidal X).toMonoidalCategoryStruct = monoidalStruct H C X
  symmetric : ∀ X : Scheme.{0}, letI := monoidal X; SymmetricCategory (DivisorObject X)
  unit_eq : ∀ X : Scheme.{0}, letI := monoidal X; (𝟙_ (DivisorObject X)) = DivisorObject.unitObject X
  tensor_eq : ∀ (X : Scheme.{0}) (L M : DivisorObject X), letI := monoidal X; L ⊗ M = tensor H X L M
  symmetry_eq : ∀ (X : Scheme.{0}) (L M : DivisorObject X),
    letI := monoidal X
    letI := symmetric X
    (β_ L M).hom = eqToHom (tensor_eq X L M) ≫ (symmetry H C X L M).hom ≫
      eqToHom (tensor_eq X M L).symm
  pullbackTensorData : ∀ {X Y : Scheme.{0}} (f : Y ⟶ X), PullbackTensorData f
  pullbackMonoidal : ∀ {X Y : Scheme.{0}} (f : Y ⟶ X),
    letI := monoidal X
    letI := monoidal Y
    (pullbackFunctor H f).Monoidal
  pullback_unit : ∀ {X Y : Scheme.{0}} (f : Y ⟶ X),
    letI := monoidal X
    letI := monoidal Y
    letI := pullbackMonoidal f
    Functor.LaxMonoidal.ε (pullbackFunctor H f) =
      eqToHom (unit_eq Y) ≫ pullbackUnit H f ≫ (pullbackFunctor H f).map (eqToHom (unit_eq X).symm)
  pullback_tensor : ∀ {X Y : Scheme.{0}} (f : Y ⟶ X) (L M : DivisorObject X),
    letI := monoidal X
    letI := monoidal Y
    letI := pullbackMonoidal f
    Functor.LaxMonoidal.μ (pullbackFunctor H f) L M =
      eqToHom (tensor_eq Y (pullback H f L) (pullback H f M)) ≫
        pullbackTensor H C f (pullbackTensorData f) L M ≫
          (pullbackFunctor H f).map (eqToHom (tensor_eq X L M).symm)
  pullbackIdentity : ∀ X : Scheme.{0}, pullbackFunctor H (𝟙 X) ≅ 𝟭 (DivisorObject X)
  identity_module : ∀ (X : Scheme.{0}) (L : DivisorObject X),
    ((pullbackIdentity X).hom.app L).iso.hom = (Scheme.Modules.pullbackId X).hom.app L.module
  pullbackComposition : ∀ {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X),
    pullbackFunctor H g ⋙ pullbackFunctor H f ≅ pullbackFunctor H (f ≫ g)
  composition_module : ∀ {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (L : DivisorObject X),
    ((pullbackComposition f g).hom.app L).iso.hom = (Scheme.Modules.pullbackComp f g).hom.app L.module

structure NativeDivisors where
  landing : Landing
  coherence : Coherence landing
  realization : Realization landing coherence

end MathlibExt.AlgebraicGeometry.DivisorNativeOperations

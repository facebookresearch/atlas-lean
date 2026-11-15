/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Algebra.Category.ModuleCat.PresheafTensorLocality
public import MathlibExt.AlgebraicGeometry.DeligneFaltingsCategories

/-!
# Canonical sheafified tensor comparisons

The comparison maps are images of actual sheafification units. The
completed local-isomorphism/internal-Hom proof makes them isomorphisms.
This integrates the public Axiom source port with the fixed native Atlas
module tensor; it introduces no tensor or associator oracle.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NativeTensorComparisons
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
open MathlibExt.AlgebraicGeometry.AlgebraicLineBundleFamilies
open MathlibExt.AlgebraicGeometry.DeligneFaltingsCategories
universe u

abbrev localIso (X : Scheme.{u}) : MorphismProperty (ModulePresheaves X) :=
  (Opens.grothendieckTopology X).W.inverseImage
    (PresheafOfModules.toPresheaf X.ringCatSheaf.obj)

lemma localIso_iff (X : Scheme.{u}) {P Q : ModulePresheaves X} (f : P ⟶ Q) :
    localIso X f ↔ IsIso ((sheafifyModules X).map f) := by
  rw [localIso, PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
    (𝟙 X.ringCatSheaf.obj)]
  rfl

instance localIso_monoidal (X : Scheme.{u}) : (localIso X).IsMonoidal := by
  change ((Opens.grothendieckTopology X).W.inverseImage
    (PresheafOfModules.toPresheaf
      (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat))).IsMonoidal
  exact PresheafOfModules.isMonoidal_W_inverseImage_toPresheaf X.sheaf

lemma unit_localIso (X : Scheme.{u}) (P : ModulePresheaves X) :
    localIso X ((moduleAdjunction X).unit.app P) := by
  apply (localIso_iff X _).2
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let : IsIso adj.counit := by dsimp [adj]; infer_instance
  let f := (sheafifyModules X).map ((moduleAdjunction X).unit.app P)
  let g := adj.counit.app ((sheafifyModules X).obj P)
  have h : f ≫ g = 𝟙 _ := adj.left_triangle_components P
  let : IsIso (f ≫ g) := by rw [h]; infer_instance
  change IsIso f
  have hf : f = inv g := by
    calc
      f = f ≫ g ≫ inv g := by simp
      _ = inv g := by rw [← Category.assoc, h]; simp
  rw [hf]
  infer_instance

instance tripleLeft_isIso (X : Scheme.{u}) (L M N : X.Modules) :
    IsIso (tripleLeft X L M N) := by
  apply (localIso_iff X _).1
  exact MorphismProperty.IsMonoidal.whiskerRight
    ((moduleAdjunction X).unit.app
      (((forgetModules X).obj L) ⊗ ((forgetModules X).obj M)))
    (unit_localIso X _) ((forgetModules X).obj N)

instance tripleRight_isIso (X : Scheme.{u}) (L M N : X.Modules) :
    IsIso (tripleRight X L M N) := by
  dsimp only [tripleRight]
  rw [Functor.map_comp]
  have : IsIso ((sheafifyModules X).map
    (((forgetModules X).obj L) ◁ (moduleAdjunction X).unit.app
      (((forgetModules X).obj M) ⊗ ((forgetModules X).obj N)))) :=
    (localIso_iff X _).1 (MorphismProperty.IsMonoidal.whiskerLeft
      ((forgetModules X).obj L) _ (unit_localIso X _))
  infer_instance

/-- The actual associator on the fixed module-sheaf tensor. -/
def tensorAssociator (X : Scheme.{u}) (L M N : X.Modules) :
    moduleTensor X (moduleTensor X L M) N ≅ moduleTensor X L (moduleTensor X M N) :=
  (asIso (tripleLeft X L M N)).symm ≪≫ asIso (tripleRight X L M N)

/-- The binary sheafification comparison is the actual unit tensor map. -/
def pairComparison (X : Scheme.{u}) (P Q : ModulePresheaves X) :
    (sheafifyModules X).obj (P ⊗ Q) ⟶
      moduleTensor X ((sheafifyModules X).obj P) ((sheafifyModules X).obj Q) :=
  (sheafifyModules X).map
    ((moduleAdjunction X).unit.app P ⊗ₘ (moduleAdjunction X).unit.app Q)

instance pairComparison_isIso (X : Scheme.{u}) (P Q : ModulePresheaves X) :
    IsIso (pairComparison X P Q) := by
  apply (localIso_iff X _).1
  rw [tensorHom_def]
  exact (localIso X).comp_mem _ _
    (MorphismProperty.IsMonoidal.whiskerRight _ (unit_localIso X P) Q)
    (MorphismProperty.IsMonoidal.whiskerLeft _ _ (unit_localIso X Q))

end MathlibExt.AlgebraicGeometry.NativeTensorComparisons

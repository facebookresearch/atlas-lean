/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Algebra.Category.ModuleCat.PresheafTensorLocality
public import MathlibExt.AlgebraicGeometry.LineBundleTaskContracts

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
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
universe u

/-- The fixed module-sheafification adjunction. -/
abbrev moduleAdjunction (X : Scheme.{u}) : sheafifyModules X ⊣ forgetModules X :=
  PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)

/-- The actual left unit of the sheaf tensor. -/
def tensorLeftUnit (X : Scheme.{u}) (L : X.Modules) :
    moduleTensor X (structureModule X) L ≅ L :=
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  letI : IsIso adj.counit := by dsimp [adj]; infer_instance
  (sheafifyModules X).mapIso (λ_ ((forgetModules X).obj L)) ≪≫
    asIso (adj.counit.app L)

/-- The actual right unit of the sheaf tensor. -/
def tensorRightUnit (X : Scheme.{u}) (L : X.Modules) :
    moduleTensor X L (structureModule X) ≅ L :=
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  letI : IsIso adj.counit := by dsimp [adj]; infer_instance
  (sheafifyModules X).mapIso (ρ_ ((forgetModules X).obj L)) ≪≫
    asIso (adj.counit.app L)

/-- The actual symmetry is sheafification of presheaf symmetry. -/
def tensorSwap (X : Scheme.{u}) (L M : X.Modules) :
    moduleTensor X L M ≅ moduleTensor X M L :=
  (sheafifyModules X).mapIso (β_ ((forgetModules X).obj L) ((forgetModules X).obj M))

/-- The actual sheafification of the presheaf triple tensor. -/
abbrev tripleTensor (X : Scheme.{u}) (L M N : X.Modules) : X.Modules :=
  (sheafifyModules X).obj
    ((((forgetModules X).obj L) ⊗ ((forgetModules X).obj M)) ⊗ ((forgetModules X).obj N))

/-- The left comparison is the sheafification-unit map on the first pair. -/
def tripleLeft (X : Scheme.{u}) (L M N : X.Modules) :
    tripleTensor X L M N ⟶ moduleTensor X (moduleTensor X L M) N :=
  (sheafifyModules X).map
    (((moduleAdjunction X).unit.app
      (((forgetModules X).obj L) ⊗ ((forgetModules X).obj M))) ▷
      ((forgetModules X).obj N))

/-- The right comparison uses the actual presheaf associator and unit. -/
def tripleRight (X : Scheme.{u}) (L M N : X.Modules) :
    tripleTensor X L M N ⟶ moduleTensor X L (moduleTensor X M N) :=
  (sheafifyModules X).map
    ((α_ ((forgetModules X).obj L) ((forgetModules X).obj M)
      ((forgetModules X).obj N)).hom ≫
      (((forgetModules X).obj L) ◁ (moduleAdjunction X).unit.app
        (((forgetModules X).obj M) ⊗ ((forgetModules X).obj N))))

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

/-- Tensoring actual module isomorphisms, on the fixed sheaf tensor. -/
def tensorIso {X : Scheme.{u}} {E E' F F' : X.Modules}
    (a : E ≅ E') (b : F ≅ F') : moduleTensor X E F ≅ moduleTensor X E' F' where
  hom := tensorMap a.hom b.hom
  inv := tensorMap a.inv b.inv
  hom_inv_id := by rw [← tensorMap_comp]; simp
  inv_hom_id := by rw [← tensorMap_comp]; simp

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

section Sections

open scoped TensorProduct

variable (X : Scheme.{u})

/-- Naturality of the sheafification unit, on sections. -/
theorem unit_naturality_apply {P Q : ModulePresheaves X} (f : P ⟶ Q) (U : X.Opensᵒᵖ)
    (x : P.obj U) :
    ((forgetModules X).map ((sheafifyModules X).map f)).app' U
      (((moduleAdjunction X).unit.app P).app' U x) =
      ((moduleAdjunction X).unit.app Q).app' U (f.app' U x) :=
  congrArg (fun g : P ⟶ (forgetModules X).obj ((sheafifyModules X).obj Q) ↦ g.app' U x)
    ((moduleAdjunction X).unit_naturality f)

/-- The pair comparison sends the class of a pure tensor `p ⊗ q` to the class of `[p] ⊗ [q]`. -/
theorem pairComparison_apply_tmul (P Q : ModulePresheaves X) (U : X.Opensᵒᵖ)
    (p : P.obj U) (q : Q.obj U) :
    ((forgetModules X).map (pairComparison X P Q)).app' U
      (((moduleAdjunction X).unit.app (P ⊗ Q)).app' U (p ⊗ₜ q)) =
      ((moduleAdjunction X).unit.app
        ((forgetModules X).obj ((sheafifyModules X).obj P) ⊗
          (forgetModules X).obj ((sheafifyModules X).obj Q))).app' U
        (((moduleAdjunction X).unit.app P).app' U p ⊗ₜ
          ((moduleAdjunction X).unit.app Q).app' U q) :=
  unit_naturality_apply X
    ((moduleAdjunction X).unit.app P ⊗ₘ (moduleAdjunction X).unit.app Q) U (p ⊗ₜ q)

/-- The associator composed with the left comparison is the right comparison. -/
theorem tripleLeft_comp_tensorAssociator_hom (L M N : X.Modules) :
    tripleLeft X L M N ≫ (tensorAssociator X L M N).hom = tripleRight X L M N := by
  simp [tensorAssociator]

/-- The associator sends the class of `[a ⊗ b] ⊗ c` to the class of `a ⊗ [b ⊗ c]`. -/
theorem tensorAssociator_hom_apply_tmul (L M N : X.Modules) (U : X.Opensᵒᵖ)
    (a : ((forgetModules X).obj L).obj U) (b : ((forgetModules X).obj M).obj U)
    (c : ((forgetModules X).obj N).obj U) :
    ((forgetModules X).map (tensorAssociator X L M N).hom).app' U
      (((moduleAdjunction X).unit.app
        ((forgetModules X).obj (moduleTensor X L M) ⊗ (forgetModules X).obj N)).app' U
        (((moduleAdjunction X).unit.app
          ((forgetModules X).obj L ⊗ (forgetModules X).obj M)).app' U (a ⊗ₜ b) ⊗ₜ c)) =
      ((moduleAdjunction X).unit.app
        ((forgetModules X).obj L ⊗ (forgetModules X).obj (moduleTensor X M N))).app' U
        (a ⊗ₜ ((moduleAdjunction X).unit.app
          ((forgetModules X).obj M ⊗ (forgetModules X).obj N)).app' U (b ⊗ₜ c)) := by
  have h1 := unit_naturality_apply X
    (((moduleAdjunction X).unit.app
      (((forgetModules X).obj L) ⊗ ((forgetModules X).obj M))) ▷ ((forgetModules X).obj N))
    U ((a ⊗ₜ b) ⊗ₜ c)
  have h2 := unit_naturality_apply X
    ((α_ ((forgetModules X).obj L) ((forgetModules X).obj M) ((forgetModules X).obj N)).hom ≫
      (((forgetModules X).obj L) ◁ (moduleAdjunction X).unit.app
        (((forgetModules X).obj M) ⊗ ((forgetModules X).obj N))))
    U ((a ⊗ₜ b) ⊗ₜ c)
  have k := congrArg (fun g ↦ ((forgetModules X).map g).app' U
      (((moduleAdjunction X).unit.app
        (((forgetModules X).obj L ⊗ (forgetModules X).obj M) ⊗ (forgetModules X).obj N)).app' U
          ((a ⊗ₜ b) ⊗ₜ c))) (tripleLeft_comp_tensorAssociator_hom X L M N)
  exact (congrArg (fun y ↦ ((forgetModules X).map (tensorAssociator X L M N).hom).app' U y)
    h1).symm.trans (k.trans h2)

/-- The inverse associator sends the class of `a ⊗ [b ⊗ c]` to the class of `[a ⊗ b] ⊗ c`. -/
theorem tensorAssociator_inv_apply_tmul (L M N : X.Modules) (U : X.Opensᵒᵖ)
    (a : ((forgetModules X).obj L).obj U) (b : ((forgetModules X).obj M).obj U)
    (c : ((forgetModules X).obj N).obj U) :
    ((forgetModules X).map (tensorAssociator X L M N).inv).app' U
      (((moduleAdjunction X).unit.app
        ((forgetModules X).obj L ⊗ (forgetModules X).obj (moduleTensor X M N))).app' U
        (a ⊗ₜ ((moduleAdjunction X).unit.app
          ((forgetModules X).obj M ⊗ (forgetModules X).obj N)).app' U (b ⊗ₜ c))) =
      ((moduleAdjunction X).unit.app
        ((forgetModules X).obj (moduleTensor X L M) ⊗ (forgetModules X).obj N)).app' U
        (((moduleAdjunction X).unit.app
          ((forgetModules X).obj L ⊗ (forgetModules X).obj M)).app' U (a ⊗ₜ b) ⊗ₜ c) := by
  have h := tensorAssociator_hom_apply_tmul X L M N U a b c
  have k := congrArg (fun g ↦ ((forgetModules X).map g).app' U
      (((moduleAdjunction X).unit.app
        ((forgetModules X).obj (moduleTensor X L M) ⊗ (forgetModules X).obj N)).app' U
        (((moduleAdjunction X).unit.app
          ((forgetModules X).obj L ⊗ (forgetModules X).obj M)).app' U (a ⊗ₜ b) ⊗ₜ c)))
    (tensorAssociator X L M N).hom_inv_id
  exact (congrArg (fun y ↦ ((forgetModules X).map (tensorAssociator X L M N).inv).app' U y)
    h).symm.trans k

end Sections

end MathlibExt.AlgebraicGeometry.NativeTensorComparisons

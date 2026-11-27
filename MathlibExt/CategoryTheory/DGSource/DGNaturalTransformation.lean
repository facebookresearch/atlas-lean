/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed source port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/DG/NaturalTransformation.lean
Only module/namespace paths are adapted for Atlas; source operations and hypotheses are retained.
-/

public import MathlibExt.CategoryTheory.DGSource.DGFunctor
public import MathlibExt.CategoryTheory.DGSource.CochainBraiding
public import MathlibExt.CategoryTheory.DGSource.EnrichedNaturalTransformation

/-!
# DG natural transformations and their components

A DG natural transformation has closed degree-zero components that commute with every homogeneous
arrow. Mathlib's unit-graded `GradedNatTrans` supplies closed degree-zero components and naturality
on all degrees. Passing the components to cohomology gives a natural transformation between the
induced functors on `H⁰`.

The enriched naturality square is equivalent to its elementwise form: for every homogeneous
morphism `f` of degree `n`, `F f` followed by the component at the target equals the component at
the source followed by `G f`, with no sign since the components have degree zero
(`MathlibExt.DGSource.DGNatTrans.dgComp_dgMap_dgApp`).  Conversely, closed degree-zero components satisfying
this condition define a DG natural transformation (`MathlibExt.DGSource.DGNatTrans.ofDGApp`), and a DG
natural transformation is determined by its components (`MathlibExt.DGSource.DGNatTrans.ext_dgApp`).

## Reference

* B. Keller, *Deriving DG categories*, Section 1.
-/

public section

open CategoryTheory MonoidalCategory

universe v u₁ u₂

namespace MathlibExt.DGSource

variable {R : Type v} [CommRing R] {C : Type u₁} {D : Type u₂}
variable [MathlibExt.DGSource.DGCategory R C] [MathlibExt.DGSource.DGCategory R D]

/-- Closed degree-zero DG natural transformations, using Mathlib's graded enriched
natural transformations at the monoidal unit. -/
abbrev DGNatTrans
    (F G : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D) :=
  UnitGradedNatTrans F G

namespace DGNatTrans

/-- The identity DG natural transformation. -/
noncomputable def id (F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D) :
    DGNatTrans F F := UnitGradedNatTrans.id F

/-- Composition of DG natural transformations. -/
noncomputable def comp {F G H : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D}
    (α : DGNatTrans F G) (β : DGNatTrans G H) : DGNatTrans F H :=
  UnitGradedNatTrans.comp α β

/-- The component of the identity DG natural transformation. -/
@[simp]
theorem id_app (F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D)
    (X : C) : (id F).app X = eId _ (F.obj X) := by
  simp only [id, UnitGradedNatTrans.id_app]
  rfl

/-- The component of a composite DG natural transformation. -/
@[simp]
theorem comp_app {F G H : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D}
    (α : DGNatTrans F G) (β : DGNatTrans G H) (X : C) :
    (comp α β).app X = eHomEquiv _
      (ForgetEnrichment.homOf _ (α.app X) ≫ ForgetEnrichment.homOf _ (β.app X)) := by
  simp only [comp, UnitGradedNatTrans.comp_app]
  rfl

/-! ### Components as closed degree-zero morphisms -/

/-- The degree-zero element of a complex named by a map out of the tensor unit. -/
private noncomputable def unitElem {K : CochainComplex (ModuleCat.{v} R) ℤ}
    (a : 𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ) ⟶ K) : K.X 0 :=
  (a.f 0).hom ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (𝟙_ (ModuleCat.{v} R))).inv 1)

/-- On a degree-`n` element, the right unitor followed by composition with a map out of the
tensor unit is composition with the closed degree-zero morphism that map names. -/
private theorem rightUnitor_inv_tensorHom_eComp_apply {X Y Z : D}
    {W : CochainComplex (ModuleCat.{v} R) ℤ} (φ : W ⟶ dgHomComplex R X Y)
    (a : 𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ) ⟶ dgHomComplex R Y Z) (n : ℤ) (w : W.X n) :
    (((ρ_ W).inv ≫ (φ ⊗ₘ a) ≫ eComp _ X Y Z).f n).hom w =
      dgComp R ((φ.f n).hom w) (unitElem a) (add_zero n) := by
  simp only [HomologicalComplex.comp_f, HomologicalComplex.rightUnitor_inv_f,
    HomologicalComplex.rightUnitor'_inv, Category.assoc, tensorHom_def',
    HomologicalComplex.ι_whiskerRight_assoc, HomologicalComplex.ι_whiskerLeft_assoc,
    ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.MonoidalCategory.rightUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply, ModuleCat.MonoidalCategory.whiskerRight_apply]
  rw [unitElem, ← dgCompMap_tmul, dgCompMap_def]
  rfl

/-- On a degree-`n` element, the left unitor followed by composition after a map out of the
tensor unit is composition after the closed degree-zero morphism that map names. -/
private theorem leftUnitor_inv_tensorHom_eComp_apply {X Y Z : D}
    {W : CochainComplex (ModuleCat.{v} R) ℤ}
    (a : 𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ) ⟶ dgHomComplex R X Y)
    (φ : W ⟶ dgHomComplex R Y Z) (n : ℤ) (w : W.X n) :
    (((λ_ W).inv ≫ (a ⊗ₘ φ) ≫ eComp _ X Y Z).f n).hom w =
      dgComp R (unitElem a) ((φ.f n).hom w) (zero_add n) := by
  simp only [HomologicalComplex.comp_f, HomologicalComplex.leftUnitor_inv_f,
    HomologicalComplex.leftUnitor'_inv, Category.assoc, tensorHom_def,
    HomologicalComplex.ι_whiskerRight_assoc, HomologicalComplex.ι_whiskerLeft_assoc,
    ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply, ModuleCat.MonoidalCategory.whiskerRight_apply]
  rw [unitElem, ← dgCompMap_tmul, dgCompMap_def]
  rfl

/-- The naturality square of a family of maps out of the tensor unit holds exactly when the
closed degree-zero morphisms they name commute with the actions of the two functors on
homogeneous morphisms of every degree. -/
private theorem naturality_iff {F G : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D}
    {X Y : C} (aX : 𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ) ⟶ dgHomComplex R (F.obj X) (G.obj X))
    (aY : 𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ) ⟶ dgHomComplex R (F.obj Y) (G.obj Y)) :
    (β_ (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)) (dgHomComplex R X Y)).hom ≫
        (F.map X Y ⊗ₘ aY) ≫ eComp _ (F.obj X) (F.obj Y) (G.obj Y) =
      (aX ⊗ₘ G.map X Y) ≫ eComp _ (F.obj X) (G.obj X) (G.obj Y) ↔
    ∀ (n : ℤ) (f : DGHom R n X Y),
      dgComp R (F.dgMap n f) (unitElem aY) (add_zero n) =
        dgComp R (unitElem aX) (G.dgMap n f) (zero_add n) := by
  -- Precomposing with the left unitor turns the braiding of the tensor unit into the right
  -- unitor, after which both sides are evaluated on homogeneous morphisms.
  rw [← cancel_epi (λ_ (dgHomComplex R X Y)).inv, leftUnitor_inv_braiding_assoc]
  constructor
  · intro h n f
    have key := congrArg (fun φ ↦ (φ.f n).hom f) h
    simpa only [rightUnitor_inv_tensorHom_eComp_apply, leftUnitor_inv_tensorHom_eComp_apply,
      EnrichedFunctor.dgMap_apply] using key
  · intro h
    ext n f
    rw [rightUnitor_inv_tensorHom_eComp_apply, leftUnitor_inv_tensorHom_eComp_apply]
    simpa only [EnrichedFunctor.dgMap_apply] using h n f

/-- The element named by the underlying morphism of a closed degree-zero morphism is that
morphism. -/
private theorem unitElem_eHomEquiv_dgClosedHomOf {X Y : D} (f : DGHom R 0 X Y)
    (hf : f ∈ dgCycles R X Y) :
    unitElem (K := dgHomComplex R X Y)
      (eHomEquiv (CochainComplex (ModuleCat.{v} R) ℤ) (dgClosedHomOf R f hf)) = f :=
  (dgClosedHom_def R _).symm.trans (dgClosedHom_dgClosedHomOf R f hf)

variable {F G : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D}

/-- The **component** of a DG natural transformation at an object, as a closed degree-zero
morphism. -/
noncomputable def dgApp (α : DGNatTrans F G) (X : C) : DGHom R 0 (F.obj X) (G.obj X) :=
  unitElem (α.app X)

/-- The component of a DG natural transformation is the closed degree-zero morphism underlying its
enriched component. -/
theorem dgApp_eq_dgClosedHom (α : DGNatTrans F G) (X : C) :
    α.dgApp X = dgClosedHom R (ForgetEnrichment.homOf _ (α.app X)) :=
  (dgClosedHom_def R _).symm

/-- The component of a DG natural transformation is closed. -/
theorem dgApp_mem_dgCycles (α : DGNatTrans F G) (X : C) :
    α.dgApp X ∈ dgCycles R (F.obj X) (G.obj X) := by
  rw [dgApp_eq_dgClosedHom]
  exact dgClosedHom_mem_dgCycles R _

/-- **Naturality of a DG natural transformation** on homogeneous morphisms of every degree: for
`f` of degree `n`, `F f` followed by the component at the target is the component at the source
followed by `G f`. -/
theorem dgComp_dgMap_dgApp (α : DGNatTrans F G) {X Y : C} {n : ℤ} (f : DGHom R n X Y) :
    dgComp R (F.dgMap n f) (α.dgApp Y) (add_zero n) =
      dgComp R (α.dgApp X) (G.dgMap n f) (zero_add n) :=
  (naturality_iff (α.app X) (α.app Y)).1 (α.naturality X Y) n f

/-- DG natural transformations are determined by their components. -/
theorem ext_dgApp {α β : DGNatTrans F G} (h : ∀ X, α.dgApp X = β.dgApp X) : α = β := by
  apply GradedNatTrans.ext
  funext X
  have := congrArg (ForgetEnrichment.homTo (CochainComplex (ModuleCat.{v} R) ℤ))
    (dgClosedHom_injective R (by simpa only [dgApp_eq_dgClosedHom] using h X))
  -- `homTo` and `homOf` are mutually inverse identifications of the same morphisms.
  exact this

/-- The **DG natural transformation with prescribed components**: closed degree-zero morphisms
`η X : F X ⟶ G X` which commute with the actions of `F` and `G` on homogeneous morphisms of every
degree. -/
noncomputable def ofDGApp (η : ∀ X, DGHom R 0 (F.obj X) (G.obj X))
    (hη : ∀ X, η X ∈ dgCycles R (F.obj X) (G.obj X))
    (naturality : ∀ {X Y : C} (n : ℤ) (f : DGHom R n X Y),
      dgComp R (F.dgMap n f) (η Y) (add_zero n) = dgComp R (η X) (G.dgMap n f) (zero_add n)) :
    DGNatTrans F G where
  app X := eHomEquiv _ (dgClosedHomOf R (η X) (hη X))
  naturality X Y := by
    dsimp only [Center.ofBraided, Center.ofBraidedObj]
    refine (naturality_iff _ _).2 fun n f ↦ ?_
    rw [unitElem_eHomEquiv_dgClosedHomOf, unitElem_eHomEquiv_dgClosedHomOf]
    exact naturality n f

/-- The components of the DG natural transformation with prescribed components are the
prescribed ones. -/
@[simp]
theorem dgApp_ofDGApp (η : ∀ X, DGHom R 0 (F.obj X) (G.obj X))
    (hη : ∀ X, η X ∈ dgCycles R (F.obj X) (G.obj X))
    (naturality : ∀ {X Y : C} (n : ℤ) (f : DGHom R n X Y),
      dgComp R (F.dgMap n f) (η Y) (add_zero n) = dgComp R (η X) (G.dgMap n f) (zero_add n))
    (X : C) :
    (ofDGApp η hη naturality).dgApp X = η X :=
  unitElem_eHomEquiv_dgClosedHomOf (η X) (hη X)

/-- The components of the identity DG natural transformation are identities. -/
@[simp]
theorem dgApp_id (F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D) (X : C) :
    (DGNatTrans.id F).dgApp X = dgId R (F.obj X) := by
  rw [dgApp_eq_dgClosedHom, id_app, ForgetEnrichment.homOf_eId, dgClosedHom_id]
  -- `ForgetEnrichment.to` is the identity on objects.
  rfl

/-- The components of a composite DG natural transformation are the composites of the
components. -/
@[simp]
theorem dgApp_comp {H : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D}
    (α : DGNatTrans F G) (β : DGNatTrans G H) (X : C) :
    (comp α β).dgApp X = dgCompZero R (α.dgApp X) (β.dgApp X) := by
  simp only [dgApp_eq_dgClosedHom, comp_app]
  -- `eHomEquiv` is the identity on the underlying category of the enrichment.
  exact dgClosedHom_comp (C := D) R _ _

end DGNatTrans

/-- DG functors with closed degree-zero DG natural transformations as morphisms. -/
@[ext]
structure DGFunctor (R : Type v) [CommRing R] (C : Type u₁) (D : Type u₂)
    [MathlibExt.DGSource.DGCategory R C] [MathlibExt.DGSource.DGCategory R D] where
  /-- The underlying functor enriched in cochain complexes. -/
  toEnrichedFunctor : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D

noncomputable instance : Category (DGFunctor R C D) where
  Hom F G := DGNatTrans F.toEnrichedFunctor G.toEnrichedFunctor
  id F := DGNatTrans.id F.toEnrichedFunctor
  comp α β := DGNatTrans.comp α β
  id_comp := by
    intro F G α
    apply GradedNatTrans.ext
    funext X
    simp [DGNatTrans.comp_app, DGNatTrans.id_app, eHomEquiv]
    rfl
  comp_id := by
    intro F G α
    apply GradedNatTrans.ext
    funext X
    simp [DGNatTrans.comp_app, DGNatTrans.id_app, eHomEquiv]
    rfl
  assoc := by
    intro F G H I α β γ
    apply GradedNatTrans.ext
    funext X
    simp only [DGNatTrans.comp_app, eHomEquiv]
    -- Composition of unit-shaped components reduces to ordinary composition in `Z⁰`.
    change (ForgetEnrichment.homOf _ (α.app X) ≫
        ForgetEnrichment.homOf _ (β.app X)) ≫
        ForgetEnrichment.homOf _ (γ.app X) =
      ForgetEnrichment.homOf _ (α.app X) ≫
        (ForgetEnrichment.homOf _ (β.app X) ≫
          ForgetEnrichment.homOf _ (γ.app X))
    exact Category.assoc _ _ _

namespace DGNatTrans

/-- The component of a DG natural transformation on the homotopy category is the
homotopy class of its closed degree-zero component. -/
noncomputable def mapDGHomotopyCategory
    {F G : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D}
    (α : DGNatTrans F G) :
    F.mapDGHomotopyCategory ⟶ G.mapDGHomotopyCategory where
  app X := (MathlibExt.DGSource.dgClosedToHomotopy (C := D) R).map
    (ForgetEnrichment.homOf (C := D) (CochainComplex (ModuleCat.{v} R) ℤ)
      (α.app (MathlibExt.DGSource.DGHomotopyCategory.underlying R X)))
  naturality := by
    intro X Y f
    rcases X with ⟨X⟩
    rcases Y with ⟨Y⟩
    obtain ⟨g, hg, rfl⟩ := MathlibExt.DGSource.exists_dgHomotopyClass_eq R f
    have h := congrArg (fun q => (MathlibExt.DGSource.dgClosedToHomotopy (C := D) R).map q)
      ((UnitGradedNatTrans.toOrdinary α).naturality
        (MathlibExt.DGSource.dgClosedHomOf R g hg))
    simp only [UnitGradedNatTrans.toOrdinary_app] at h
    rw [Functor.map_comp, Functor.map_comp] at h
    have hmap (J : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D) :
        (MathlibExt.DGSource.dgClosedToHomotopy (C := D) R).map
          (J.forget.map (MathlibExt.DGSource.dgClosedHomOf R g hg)) =
          J.mapDGHomotopyCategory.map (MathlibExt.DGSource.dgHomotopyClass R g hg) := by
      simp only [EnrichedFunctor.forget_map]
      simp only [MathlibExt.DGSource.dgClosedToHomotopy_map, MathlibExt.DGSource.DGHomotopyCategory.homOf_def]
      simp only [J.dgClosedHom_forget_map]
      simp only [MathlibExt.DGSource.dgClosedHom_dgClosedHomOf, J.mapDGHomotopyCategory_map,
        MathlibExt.DGSource.homologyMap_dgHomotopyClass, J.dgMap_apply, ForgetEnrichment.to_of]
      rfl
    rw [← hmap F, ← hmap G]
    -- The forgetful object wrappers reduce to the same DG objects.
    exact h

/-- On an object, the induced transformation is the homotopy class of the closed component. -/
@[simp]
theorem mapDGHomotopyCategory_app
    {F G : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D}
    (α : DGNatTrans F G)
    (X : C) :
    (mapDGHomotopyCategory α).app (MathlibExt.DGSource.DGHomotopyCategory.of R X) =
      MathlibExt.DGSource.DGHomotopyCategory.homOf R
        (MathlibExt.DGSource.dgClosedHom R
          (ForgetEnrichment.homOf (C := D) (CochainComplex (ModuleCat.{v} R) ℤ)
            (α.app X)))
        (MathlibExt.DGSource.dgClosedHom_mem_dgCycles R _) := by
  unfold mapDGHomotopyCategory
  dsimp only [MathlibExt.DGSource.DGHomotopyCategory.underlying_of]
  exact MathlibExt.DGSource.dgClosedToHomotopy_map R _

/-- A component of the induced transformation vanishes exactly when the corresponding closed
degree-zero DG morphism is a boundary. -/
-- This remains outside `simp`: `mapDGHomotopyCategory_app` already reduces its left side.
theorem mapDGHomotopyCategory_app_eq_zero_iff
    {F G : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D}
    (α : DGNatTrans F G)
    (X : C) :
    (mapDGHomotopyCategory α).app (MathlibExt.DGSource.DGHomotopyCategory.of R X) = 0 ↔
      MathlibExt.DGSource.dgClosedHom R
        (ForgetEnrichment.homOf (C := D) (CochainComplex (ModuleCat.{v} R) ℤ)
          (α.app X)) ∈
          MathlibExt.DGSource.dgBoundaries R (F.obj X) (G.obj X) := by
  unfold mapDGHomotopyCategory
  dsimp only [MathlibExt.DGSource.DGHomotopyCategory.underlying_of]
  exact MathlibExt.DGSource.dgClosedToHomotopy_map_eq_zero_iff (C := D) R _

/-- Passing the identity DG transformation to `H⁰` gives the identity transformation. -/
@[simp]
theorem mapDGHomotopyCategory_id
    (F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D) :
    mapDGHomotopyCategory (DGNatTrans.id F) = 𝟙 F.mapDGHomotopyCategory := by
  ext X
  rcases X with ⟨X⟩
  simp only [mapDGHomotopyCategory, NatTrans.id_app, DGNatTrans.id_app]
  -- The identity component is the enriched identity after forgetting enrichment.
  exact (MathlibExt.DGSource.dgClosedToHomotopy (C := D) R).map_id _

/-- Passing a composite of DG transformations to `H⁰` composes their images. -/
@[simp]
theorem mapDGHomotopyCategory_comp
    {F G H : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D}
    (α : DGNatTrans F G) (β : DGNatTrans G H) :
    mapDGHomotopyCategory (DGNatTrans.comp α β) =
      mapDGHomotopyCategory α ≫ mapDGHomotopyCategory β := by
  ext X
  rcases X with ⟨X⟩
  simp only [mapDGHomotopyCategory, NatTrans.comp_app, DGNatTrans.comp_app]
  -- The composite's unit-graded component is ordinary composition under `homOf`.
  exact (MathlibExt.DGSource.dgClosedToHomotopy (C := D) R).map_comp _ _

end DGNatTrans

/-- Taking `H⁰` sends DG functors and DG natural transformations to ordinary functors and
natural transformations. -/
@[expose]
noncomputable def mapDGHomotopyCategoryFunctor :
    DGFunctor R C D ⥤
      (MathlibExt.DGSource.DGHomotopyCategory R C ⥤ MathlibExt.DGSource.DGHomotopyCategory R D) where
  obj F := F.toEnrichedFunctor.mapDGHomotopyCategory
  map α := DGNatTrans.mapDGHomotopyCategory α
  map_id F := DGNatTrans.mapDGHomotopyCategory_id F.toEnrichedFunctor
  map_comp α β := DGNatTrans.mapDGHomotopyCategory_comp α β

/-- On objects, the functor takes a DG functor to its induced functor on `H⁰`. -/
@[simp]
theorem mapDGHomotopyCategoryFunctor_obj (F : DGFunctor R C D) :
    mapDGHomotopyCategoryFunctor.obj F = F.toEnrichedFunctor.mapDGHomotopyCategory :=
  (rfl)

/-- On morphisms, the functor takes a DG transformation to its induced transformation on `H⁰`. -/
@[simp]
theorem mapDGHomotopyCategoryFunctor_map {F G : DGFunctor R C D} (α : F ⟶ G) :
    mapDGHomotopyCategoryFunctor.map α = DGNatTrans.mapDGHomotopyCategory α :=
  (rfl)

end MathlibExt.DGSource

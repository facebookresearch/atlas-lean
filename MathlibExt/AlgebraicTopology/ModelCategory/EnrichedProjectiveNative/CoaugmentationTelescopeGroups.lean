/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.CoaugmentationTelescopeModel
import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup.NativeWeakDetection

/-!
# Actual homotopy maps of the native input-coaugmentation telescope

Every original stage map of a level weak input is level weak when its
actual endofunctor preserves that class. The original closed telescope
comparisons carry these maps to every homotopy degree. Based tails cover
each physical point beyond any requested stage bound. Their original
point maps therefore detect the complete native level weak class.

All diagrams use the actual input transition `F^n(η_X)`, the original
interval mapping cylinders and the same chosen telescope. No weakness
of the coaugmentation, source cofibrancy or Ω endpoint is required.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CGWH.modelCategory

namespace PointedCGWH.EnrichedCoaugmentationTelescope

/-- The original pointed arrow induces an isomorphism in its literal homotopy degree. -/
theorem piN_map_isIso_of_right_weak (k : ℕ)
    {A C : PointedCGWH.{u, v}} (g : A ⟶ C)
    (hg : CGWH.weakHomotopyEquivalences g.right) :
    IsIso ((piNFunctor k).map g) := by
  have hW : WeakEquivalence g :=
    (PointedCGWH.weakEquivalence_iff g).mpr
      ((CGWH.modelCategory.weakEquivalence_iff g.right).mpr hg)
  apply (CategoryTheory.isIso_iff_bijective _).mpr
  change Function.Bijective (piNMap k g)
  have hfun : ⇑(piNEquivOfWeakEquivalence k g hW) = piNMap k g := by
    funext q
    exact piNEquivOfWeakEquivalence_apply k g hW q
  rw [← hfun]
  exact (piNEquivOfWeakEquivalence k g hW).bijective

/-- Given point equations transport the same whole original underlying map. -/
theorem piN_map_isIso_at_original_point (k : ℕ)
    {A C : CGWH.{u, v}} (f : A ⟶ C) {p : A} {q : C}
    (g : pointedAt A p ⟶ pointedAt C q) (hRight : g.right = f)
    (x : A) (hSource : p = x) (hTarget : q = f x)
    (hIso : IsIso ((piNFunctor k).map g)) :
    IsIso ((piNFunctor k).map (pointedAtMap f x (f x) rfl)) := by
  subst p
  subst q
  have hg : g = pointedAtMap f x (f x) rfl := by
    apply pointedToCGWH.map_injective
    exact hRight
  rw [← hg]
  exact hIso

attribute [local instance] PointedCGWH.PointedAtGeometry.pointedNatColimits

/-- The actual Type colimit map retains each original weak pointed stage map. -/
theorem piN_colim_map_isIso_of_pointwise_right_weak (k : ℕ)
    {D E : ℕ ⥤ PointedCGWH.{u, v}} (α : D ⟶ E)
    (hα : ∀ n : ℕ, CGWH.weakHomotopyEquivalences (α.app n).right) :
    IsIso (colim.map (Functor.whiskerRight α (piNFunctor k))) := by
  let τ := Functor.whiskerRight α (piNFunctor k)
  have : ∀ n : ℕ, IsIso (τ.app n) :=
    fun n => piN_map_isIso_of_right_weak k (α.app n) (hα n)
  have : IsIso τ := NatIso.isIso_of_isIso_app τ
  change IsIso (colim.map τ)
  infer_instance

/-- The existing whole enriched carrier, with every original action and universe. -/
abbrev Carrier (I : Type) [EnrichedCategory PointedCGWH.{u, v} I] :=
  EnrichedFunctorCat PointedCGWH.{u, v} I

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {F : Carrier.{u, v} I ⥤ Carrier.{u, v} I}
  (η : 𝟭 (Carrier.{u, v} I) ⟶ F)

attribute [local instance] MonoidalClosed.enrichedCategorySelf
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- All literal homotopy degrees retain the original selected telescope component map. -/
theorem telescope_map_piN_isIso
    (hF : ∀ {A C : Carrier.{u, v} I} (g : A ⟶ C),
      weakEquivalences (Carrier.{u, v} I) g →
        weakEquivalences (Carrier.{u, v} I) (F.map g))
    {X Y : Carrier.{u, v} I} (f : X ⟶ Y)
    (hf : weakEquivalences (Carrier.{u, v} I) f) (a : I) (k : ℕ) :
    IsIso ((piNFunctor k).map (component ((telescopeFunctor η).map f) a)) := by
  let α := Functor.whiskerRight (diagramMap η f) (evaluation a)
  have hα (n : ℕ) : CGWH.weakHomotopyEquivalences (α.app n).right := by
    change CGWH.weakHomotopyEquivalences
      (component ((stage η n).functor.map f) a).right
    exact (weakEquivalences_iff_components _).mp
      (stage_map_mem_weak η f n (iterate_map_mem_weak hF f hf n)) a
  have hcolim : IsIso (colim.map (Functor.whiskerRight α (piNFunctor k))) :=
    piN_colim_map_isIso_of_pointwise_right_weak k α hα
  let e : colimit (evaluatedDiagram η X a ⋙ piNFunctor k) ≅
      piN k ((telescope η X).toEnrichedFunctor.obj a) := typeHomotopyIso η X a k
  let e' : colimit (evaluatedDiagram η Y a ⋙ piNFunctor k) ≅
      piN k ((telescope η Y).toEnrichedFunctor.obj a) := typeHomotopyIso η Y a k
  have hSource : IsIso e.hom := e.isIso_hom
  have hComposite : IsIso (colim.map (Functor.whiskerRight α (piNFunctor k)) ≫ e'.hom) :=
    IsIso.comp_isIso' hcolim e'.isIso_hom
  exact @IsIso.of_isIso_fac_left _ _ _ _ _ e.hom
    ((piNFunctor k).map (component ((telescopeFunctor η).map f) a))
    (colim.map (Functor.whiskerRight α (piNFunctor k)) ≫ e'.hom) hSource hComposite
    (typeHomotopyIso_naturality η f a k).symm

/-- Every original based tail and degree retain the original telescope map and its image point. -/
theorem basedTail_map_piN_isIso
    (hF : ∀ {A C : Carrier.{u, v} I} (g : A ⟶ C),
      weakEquivalences (Carrier.{u, v} I) g →
        weakEquivalences (Carrier.{u, v} I) (F.map g))
    {X Y : Carrier.{u, v} I} (f : X ⟶ Y)
    (hf : weakEquivalences (Carrier.{u, v} I) f)
    (a : I) (r k : ℕ)
    (p : (((stage η r).functor.obj X).toEnrichedFunctor.obj a).right) :
    IsIso ((piNFunctor k).map (basedTailCoconeMap η f a r p)) := by
  let α := basedTailMap η f a r p
  have hα (n : ℕ) : CGWH.weakHomotopyEquivalences (α.app n).right := by
    change CGWH.weakHomotopyEquivalences ((basedTailMap η f a r p).app n).right
    rw [basedTailMap_right]
    exact (weakEquivalences_iff_components _).mp
      (stage_map_mem_weak η f (r + n) (iterate_map_mem_weak hF f hf (r + n))) a
  have hcolim : IsIso (colim.map (Functor.whiskerRight α (piNFunctor k))) :=
    piN_colim_map_isIso_of_pointwise_right_weak k α hα
  let q : (((stage η r).functor.obj Y).toEnrichedFunctor.obj a).right :=
    (component ((stage η r).functor.map f) a).right p
  let e : colimit (basedTailDiagram η X a r p ⋙ piNFunctor k) ≅
      (piNFunctor k).obj (basedTailCocone η X a r p).pt := basedTailTypeIso η X a r k p
  let e' : colimit (basedTailDiagram η Y a r q ⋙ piNFunctor k) ≅
      (piNFunctor k).obj (basedTailCocone η Y a r q).pt := basedTailTypeIso η Y a r k q
  have hSource : IsIso e.hom := e.isIso_hom
  have hComposite : IsIso (colim.map (Functor.whiskerRight α (piNFunctor k)) ≫ e'.hom) :=
    IsIso.comp_isIso' hcolim e'.isIso_hom
  exact @IsIso.of_isIso_fac_left _ _ _ _ _ e.hom
    ((piNFunctor k).map (basedTailCoconeMap η f a r p))
    (colim.map (Functor.whiskerRight α (piNFunctor k)) ≫ e'.hom) hSource hComposite
    (basedTailTypeIso_naturality η f a r k p).symm

/-- Every physical source point and homotopy degree retain the actual native telescope map. -/
private theorem telescope_map_piN_at_point_isIso_from_bound
    (hF : ∀ {A C : Carrier.{u, v} I} (g : A ⟶ C),
      weakEquivalences (Carrier.{u, v} I) g →
        weakEquivalences (Carrier.{u, v} I) (F.map g))
    {X Y : Carrier.{u, v} I} (f : X ⟶ Y)
    (hf : weakEquivalences (Carrier.{u, v} I) f)
    (a : I) (k n₀ : ℕ)
    (x : ((telescope η X).toEnrichedFunctor.obj a).right) :
    IsIso ((piNFunctor k).map
      (pointedAtMap (component ((telescopeFunctor η).map f) a).right x
        ((component ((telescopeFunctor η).map f) a).right x) rfl)) := by
  obtain ⟨r, _hr, p, hx⟩ := exists_stage_point_after η X a x n₀
  let t := component ((telescopeFunctor η).map f) a
  let q := (component ((stage η r).functor.map f) a).right p
  have hy : (component (leg η Y r) a).right q = t.right x := by
    have h := ConcreteCategory.congr_hom
      (pointedToCGWH.congr_map (evaluatedCocone_naturality η f a r)) p
    change t.right ((component (leg η X r) a).right p) =
      (component (leg η Y r) a).right q at h
    rw [hx] at h
    exact h.symm
  have hIso : IsIso ((piNFunctor k).map (basedTailCoconeMap η f a r p)) :=
    basedTail_map_piN_isIso η hF f hf a r k p
  exact piN_map_isIso_at_original_point k t.right
    (basedTailCoconeMap η f a r p) (basedTailCoconeMap_right η f a r p)
    x hx hy hIso

/-- Every requested bound has an original stage point, its literal image, and a based-tail isomorphism. -/
theorem exists_basedTail_map_piN_isIso_after
    (hF : ∀ {A C : Carrier.{u, v} I} (g : A ⟶ C),
      weakEquivalences (Carrier.{u, v} I) g →
        weakEquivalences (Carrier.{u, v} I) (F.map g))
    {X Y : Carrier.{u, v} I} (f : X ⟶ Y)
    (hf : weakEquivalences (Carrier.{u, v} I) f)
    (a : I) (k n₀ : ℕ)
    (x : ((telescope η X).toEnrichedFunctor.obj a).right) :
    ∃ (r : ℕ), n₀ ≤ r ∧
      ∃ (p : (((stage η r).functor.obj X).toEnrichedFunctor.obj a).right),
        (component (leg η X r) a).right p = x ∧
        (component (leg η Y r) a).right
          ((component ((stage η r).functor.map f) a).right p) =
            (component ((telescopeFunctor η).map f) a).right x ∧
        IsIso ((piNFunctor k).map (basedTailCoconeMap η f a r p)) := by
  obtain ⟨r, hr, p, hx⟩ := exists_stage_point_after η X a x n₀
  let t := component ((telescopeFunctor η).map f) a
  let q := (component ((stage η r).functor.map f) a).right p
  have hy : (component (leg η Y r) a).right q = t.right x := by
    have h := ConcreteCategory.congr_hom
      (pointedToCGWH.congr_map (evaluatedCocone_naturality η f a r)) p
    change t.right ((component (leg η X r) a).right p) =
      (component (leg η Y r) a).right q at h
    rw [hx] at h
    exact h.symm
  have hIso : IsIso ((piNFunctor k).map (basedTailCoconeMap η f a r p)) :=
    basedTail_map_piN_isIso η hF f hf a r k p
  exact ⟨r, hr, p, hx, hy, hIso⟩

/-- The compatible point-map API uses the original zero-bound specialization. -/
theorem telescope_map_piN_at_point_isIso
    (hF : ∀ {A C : Carrier.{u, v} I} (g : A ⟶ C),
      weakEquivalences (Carrier.{u, v} I) g →
        weakEquivalences (Carrier.{u, v} I) (F.map g))
    {X Y : Carrier.{u, v} I} (f : X ⟶ Y)
    (hf : weakEquivalences (Carrier.{u, v} I) f)
    (a : I) (k : ℕ)
    (x : ((telescope η X).toEnrichedFunctor.obj a).right) :
    IsIso ((piNFunctor k).map
      (pointedAtMap (component ((telescopeFunctor η).map f) a).right x
        ((component ((telescopeFunctor η).map f) a).right x) rfl)) := by
  obtain ⟨r, _hr, p, hx, hy, hIso⟩ :=
    exists_basedTail_map_piN_isIso_after η hF f hf a k 0 x
  exact piN_map_isIso_at_original_point k
    (component ((telescopeFunctor η).map f) a).right
    (basedTailCoconeMap η f a r p) (basedTailCoconeMap_right η f a r p)
    x hx hy hIso

/-- The actual entire input-coaugmentation telescope preserves the original native level class. -/
theorem telescopeFunctor_map_mem_weak_of_preserves
    (hF : ∀ {A C : Carrier.{u, v} I} (g : A ⟶ C),
      weakEquivalences (Carrier.{u, v} I) g →
        weakEquivalences (Carrier.{u, v} I) (F.map g))
    {X Y : Carrier.{u, v} I} (f : X ⟶ Y)
    (hf : weakEquivalences (Carrier.{u, v} I) f) :
    weakEquivalences (Carrier.{u, v} I) ((telescopeFunctor η).map f) := by
  apply (weakEquivalences_iff_components _).mpr
  intro a
  let t := component ((telescopeFunctor η).map f) a
  apply PointedCGWH.NativeAllPointWeakDetectionGeometry.weak_of_component_and_all_point_pi t
  · exact (CategoryTheory.isIso_iff_bijective _).mp
      (telescope_map_piN_isIso η hF f hf a 0)
  · intro x n
    exact (CategoryTheory.isIso_iff_bijective _).mp
      (telescope_map_piN_at_point_isIso η hF f hf a (n + 1) x)

end PointedCGWH.EnrichedCoaugmentationTelescope

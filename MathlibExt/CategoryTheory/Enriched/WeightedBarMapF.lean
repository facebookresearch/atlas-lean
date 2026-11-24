/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Enriched.WeightedBarSimplicial

/-!
# Diagram-variable maps of the strict ordinary weighted bar

This module gives the diagram-variable (`F`) functoriality packet for the
strict ordinary weighted bar: total face and degeneracy naturality from the
component lemmas, plus the bundled data and simplicial maps with their
identity/composition laws.

Nonclaims: no `W`-variance, no mixed squares, no comparisons, and no
realization, homotopy-colimit, or model-category conclusion. Weight naturality
is in `WeightedBarMapW`; the mixed square is in `WeightedBarMapFW`; categorical
packaging is in `WeightedBarFunctor`.
-/

@[expose] public section

namespace CategoryTheory
namespace StrictOrdinaryWeightedBar

universe vJ uJ vC uC uW

variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C]

/-- Total face naturality in the diagram variable, by zero/last/interior dispatch. -/
theorem wbarδ_mapF (W : Jᵒᵖ ⥤ Type uW) (F G : J ⥤ C) (n : ℕ) (i : Fin (n + 2))
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => G.obj p.1.left)]
    (φ : F ⟶ G) :
    wbarδ W F n i ≫ wbarMapF (W := W) n φ =
      wbarMapF (W := W) (n + 1) φ ≫ wbarδ W G n i := by
  by_cases h0 : i = 0
  · subst h0
    rw [wbarδ_zero, wbarδ_zero]
    exact wbarFaceZero_mapF W F G n φ
  · by_cases hlast : i = Fin.last (n + 1)
    · subst hlast
      rw [wbarδ_last, wbarδ_last]
      exact wbarFaceLast_mapF W F G n φ
    · have : NeZero (n + 1) := ⟨by omega⟩
      rw [wbarδ_inner _ _ _ i h0 hlast, wbarδ_inner _ _ _ i h0 hlast]
      exact wbarFaceInner_mapF W F G n i h0 hlast φ

/-- Total degeneracy naturality in the diagram variable, from the interior packet. -/
theorem wbarσ_mapF (W : Jᵒᵖ ⥤ Type uW) (F G : J ⥤ C) (n : ℕ) (i : Fin (n + 1))
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => G.obj p.1.left)]
    (φ : F ⟶ G) :
    wbarσ W F n i ≫ wbarMapF (W := W) (n + 1) φ =
      wbarMapF (W := W) n φ ≫ wbarσ W G n i := by
  have : NeZero (n + 1) := ⟨by omega⟩
  unfold wbarσ
  exact wbarDegInner_mapF W F G n i φ

/-- Bundled data map in the diagram variable. -/
noncomputable def wbarDataMapF (W : Jᵒᵖ ⥤ Type uW) {F G : J ⥤ C}
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => G.obj p.1.left)]
    (φ : F ⟶ G) : wbarData W F ⟶ wbarData W G where
  app n := wbarMapF (W := W) n φ
  w_δ := fun i => (wbarδ_mapF W F G _ i φ).symm
  w_σ := fun i => (wbarσ_mapF W F G _ i φ).symm

/-- Degree computation for the bundled data map. -/
@[simp]
theorem wbarDataMapF_app (W : Jᵒᵖ ⥤ Type uW) {F G : J ⥤ C}
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => G.obj p.1.left)]
    (φ : F ⟶ G) (n : ℕ) :
    (wbarDataMapF W φ).app n = wbarMapF (W := W) n φ :=
  rfl

/-- Bundled simplicial map in the diagram variable. -/
noncomputable def wbarSimplicialMapF (W : Jᵒᵖ ⥤ Type uW) {F G : J ⥤ C}
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => G.obj p.1.left)]
    (φ : F ⟶ G) : wbarSimplicial W F ⟶ wbarSimplicial W G :=
  SimplicialObject.Data.toSimplicialFunctor.map (wbarDataMapF W φ)

/-- Degree computation for the bundled simplicial map. -/
@[simp]
theorem wbarSimplicialMapF_app_mk (W : Jᵒᵖ ⥤ Type uW) {F G : J ⥤ C}
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => G.obj p.1.left)]
    (φ : F ⟶ G) (n : ℕ) :
    (wbarSimplicialMapF W φ).app (Opposite.op (SimplexCategory.mk n)) =
      wbarMapF (W := W) n φ := by
  unfold wbarSimplicialMapF
  rw [SimplicialObject.Data.toSimplicialFunctor_map_app_mk, wbarDataMapF_app]

/-- Data map preserves identities in the diagram variable. -/
@[simp]
theorem wbarDataMapF_id (W : Jᵒᵖ ⥤ Type uW) (F : J ⥤ C)
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)] :
    wbarDataMapF W (𝟙 F) = 𝟙 _ := by
  apply SimplicialObject.Data.Hom.ext
  intro n
  simp only [wbarDataMapF_app, SimplicialObject.id_app, wbarMapF_id]
  rfl

/-- Data map preserves composition in the diagram variable. -/
@[simp]
theorem wbarDataMapF_comp (W : Jᵒᵖ ⥤ Type uW) {F G H : J ⥤ C}
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => G.obj p.1.left)]
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => H.obj p.1.left)]
    (φ : F ⟶ G) (ψ : G ⟶ H) :
    wbarDataMapF W (φ ≫ ψ) = wbarDataMapF W φ ≫ wbarDataMapF W ψ := by
  apply SimplicialObject.Data.Hom.ext
  intro n
  simp only [wbarDataMapF_app, SimplicialObject.comp_app]
  exact (wbarMapF_comp n φ ψ).symm

/-- Simplicial map preserves identities in the diagram variable. -/
@[simp]
theorem wbarSimplicialMapF_id (W : Jᵒᵖ ⥤ Type uW) (F : J ⥤ C)
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)] :
    wbarSimplicialMapF W (𝟙 F) = 𝟙 _ := by
  unfold wbarSimplicialMapF
  simp only [wbarDataMapF_id, Functor.map_id]
  rfl

/-- Simplicial map preserves composition in the diagram variable. -/
@[simp]
theorem wbarSimplicialMapF_comp (W : Jᵒᵖ ⥤ Type uW) {F G H : J ⥤ C}
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => G.obj p.1.left)]
    [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => H.obj p.1.left)]
    (φ : F ⟶ G) (ψ : G ⟶ H) :
    wbarSimplicialMapF W (φ ≫ ψ) =
      wbarSimplicialMapF W φ ≫ wbarSimplicialMapF W ψ := by
  unfold wbarSimplicialMapF
  simp only [wbarDataMapF_comp, Functor.map_comp]
  rfl

end StrictOrdinaryWeightedBar
end CategoryTheory

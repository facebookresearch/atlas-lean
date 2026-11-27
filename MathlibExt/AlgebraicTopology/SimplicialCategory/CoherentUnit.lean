/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentPresentation

/-!
# The actual coherent realization unit

Every input simplex is inserted as its original enriched coherent
simplex. The operator relation proves the whole simplicial naturality,
with exactly the original vertex equations; no comparison is supplied.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization
open SimplicialEnrichment SimplicialQuiver

/-- Changing the two literal endpoint labels changes only their actual equality transports. -/
theorem simplexHom_reindex (K : SSet.{u}) {n : SimplexCategory} (σ : K.obj (op n))
    (i j : coherentSimplex.{u} n) {x y : K _⦋0⦌}
    (hx : vertex K σ i = x) (hy : vertex K σ j = y) :
    simplexHom K σ i j rfl rfl ≫ eqToHom (congrArg₂ (hom K) hx hy) =
      simplexHom K σ i j hx hy := by
  subst x
  subst y
  change simplexHom K σ i j rfl rfl ≫ 𝟙 _ = simplexHom K σ i j rfl rfl
  exact Category.comp_id _

/-- All outer simplex operators commute with the actual whole enriched-simplex insertion. -/
theorem simplexInto_operator (K : SSet.{u}) {n m : SimplexCategory} (f : n ⟶ m)
    (σ : K.obj (op m)) :
    coherentSimplexMap f ≫ simplexInto K σ = simplexInto K (K.map f.op σ) := by
  refine EnrichedFunctor.ext SSet.{u}
    (F := (coherentSimplexMap f).comp SSet.{u} (simplexInto K σ))
    (G := simplexInto K (K.map f.op σ))
    (fun i => (vertex_operator K f σ i).symm) ?_
  intro i j
  change ((coherentSimplexMap f).map i j ≫
    simplexHom K σ ((coherentSimplexMap f).obj i) ((coherentSimplexMap f).obj j) rfl rfl) ≫
      eqToHom (congrArg₂ (hom K) (vertex_operator K f σ i).symm (vertex_operator K f σ j).symm) =
        simplexHom K (K.map f.op σ) i j rfl rfl
  calc
    _ = (coherentSimplexMap f).map i j ≫
        simplexHom K σ ((coherentSimplexMap f).obj i) ((coherentSimplexMap f).obj j)
          (vertex_operator K f σ i).symm (vertex_operator K f σ j).symm :=
      (Category.assoc _ _ _).trans
        (congrArg (fun g => (coherentSimplexMap f).map i j ≫ g)
          (simplexHom_reindex K σ ((coherentSimplexMap f).obj i)
            ((coherentSimplexMap f).obj j) (vertex_operator K f σ i).symm
              (vertex_operator K f σ j).symm))
    _ = _ := by
      ext q a
      exact _root_.Quotient.sound (Closure.symm (Closure.relation
        (Equations.operator q f σ i j rfl rfl a)))

/-- The genuine unit simplicial map into the coherent nerve of the actual realization. -/
def unit (K : SSet.{u}) : K ⟶ coherentNerveFunctor.obj (realization K) where
  app n := ↾fun σ => simplexInto K σ
  naturality n m f := by
    ext σ
    exact (simplexInto_operator K f.unop σ).symm

/-- The actual unit retains every original simplex as its specified enriched coherent simplex. -/
theorem unit_app (K : SSet.{u}) (n : SimplexCategory) (σ : K.obj (op n)) :
    (unit K).app (op n) σ = simplexInto K σ := rfl

end CategoryTheory.CoherentRealization

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentNativeTriangleCell
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentAdjacentHom
import MathlibExt.AlgebraicTopology.SimplicialCategory.ComponentCategoryVertexLaws

/-!
# Original component arrows of every coherent simplex

The direct endpoint paths read individual original Hom vertices from
the actual coherent simplex. Every simplex operator preserves this
readback. Degenerate endpoints give the original identity, and the
actual direct-to-through Hom edge proves the component composition
relation of a genuine coherent triangle. No locally Kan hypothesis
or quotient of the individual object vertices is needed.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.ComponentSimplexReadback
open SimplicialEnrichment

/-- The individual ordinal-labelled original object of the coherent simplex. -/
abbrev point (n : SimplexCategory) (i : Fin (n.len + 1)) : coherentSimplex.{u} n :=
  .mk (ULift.up i)

/-- The supplied direct endpoint path, as an actual original Hom vertex. -/
def endpointVertex (n : SimplexCategory) (i j : Fin (n.len + 1)) (h : i ≤ j) :
    (point.{u} n i ⟶[SSet.{u}] point n j) _⦋0⦌ :=
  ComposableArrows.mk₀ (AdjacentHom.endpointPath (ULift.up.{u} i) (ULift.up.{u} j) h)

/-- A genuine simplex operator carries the whole original endpoint-path vertex to its direct image. -/
theorem endpointVertex_map {n m : SimplexCategory} (θ : n ⟶ m)
    (i j : Fin (n.len + 1)) (h : i ≤ j) :
    ((coherentSimplexMap.{u} θ).map (point n i) (point n j)).app (op ⦋0⦌)
        (endpointVertex n i j h) =
      endpointVertex m (θ.toOrderHom i) (θ.toOrderHom j) (θ.toOrderHom.monotone h) := by
  apply ComposableArrows.ext₀ (C := SimplicialThickening.Path
    (ULift.up.{u} (θ.toOrderHom i)) (ULift.up.{u} (θ.toOrderHom j)))
  apply SimplicialThickening.Path.ext
  change θ.toOrderHom.uliftMap '' {ULift.up.{u} i, ULift.up.{u} j} =
    {ULift.up.{u} (θ.toOrderHom i), ULift.up.{u} (θ.toOrderHom j)}
  exact Set.image_pair _ _ _

variable {C : Carrier.{u}}

/-- The same original enriched Hom vertex read from a supplied coherent simplex and ordered endpoint pair. -/
def representative {n : SimplexCategory} (σ : CoherentSimplexIn C n)
    (i j : Fin (n.len + 1)) (h : i ≤ j) :
    (σ.obj (point n i) ⟶[SSet.{u}] σ.obj (point n j)) _⦋0⦌ :=
  (σ.map (point n i) (point n j)).app (op ⦋0⦌) (endpointVertex n i j h)

/-- Every original face or degeneracy preserves the actual endpoint representative with its same labelled endpoints. -/
theorem representative_operator {n m : SimplexCategory} (θ : n ⟶ m)
    (σ : CoherentSimplexIn C m) (i j : Fin (n.len + 1)) (h : i ≤ j) :
    representative ((coherentNerveFunctor.obj C).map θ.op σ) i j h =
      representative σ (θ.toOrderHom i) (θ.toOrderHom j) (θ.toOrderHom.monotone h) := by
  change (σ.map _ _).app (op ⦋0⦌)
    (((coherentSimplexMap θ).map (point n i) (point n j)).app (op ⦋0⦌)
      (endpointVertex n i j h)) = _
  rw [endpointVertex_map]
  rfl

/-- Coincident original endpoints read the original enriched identity vertex itself. -/
theorem representative_identity {n : SimplexCategory} (σ : CoherentSimplexIn C n)
    (i : Fin (n.len + 1)) :
    representative σ i i le_rfl =
      (eId SSet.{u} (σ.obj (point n i))).app (op ⦋0⦌) PUnit.unit := by
  have h : endpointVertex.{u} n i i le_rfl =
      (eId SSet.{u} (point n i)).app (op ⦋0⦌) PUnit.unit := by
    apply ComposableArrows.ext₀
    apply SimplicialThickening.Path.ext
    change {ULift.up.{u} i, ULift.up.{u} i} = {ULift.up.{u} i}
    ext k
    simp
  exact (congrArg (fun a => (σ.map (point n i) (point n i)).app (op ⦋0⦌) a) h).trans
    congr($(σ.map_id (point n i)).app (op ⦋0⦌) PUnit.unit)

private theorem leftPath_eq :
    CompositionFace.leftPath BooleanInterval.through.{u}
      (Set.mem_univ (ULift.up.{u} (1 : Fin 3))) =
        AdjacentHom.endpointPath (ULift.up.{u} (0 : Fin 3)) (ULift.up.{u} (1 : Fin 3)) (by decide) := by
  apply AdjacentHom.path_eq
  intro k _ hk
  have h : k.down.val ≤ 1 := hk
  by_cases h0 : k.down.val = 0
  · exact Or.inl (ULift.ext (Fin.ext h0))
  · apply Or.inr
    apply ULift.ext
    apply Fin.ext
    change k.down.val = 1
    omega

private theorem rightPath_eq :
    CompositionFace.rightPath BooleanInterval.through.{u}
      (Set.mem_univ (ULift.up.{u} (1 : Fin 3))) =
        AdjacentHom.endpointPath (ULift.up.{u} (1 : Fin 3)) (ULift.up.{u} (2 : Fin 3)) (by decide) := by
  apply AdjacentHom.path_eq
  intro k hk _
  have h : 1 ≤ k.down.val := hk
  have hb : k.down.val < 3 := k.down.isLt
  by_cases h1 : k.down.val = 1
  · exact Or.inl (ULift.ext (Fin.ext h1))
  · apply Or.inr
    apply ULift.ext
    apply Fin.ext
    change k.down.val = 2
    omega

/-- The original two short endpoint representatives compose to the direct representative in the genuine
  component Hom category. -/
theorem triangle_composition (σ : CoherentSimplexIn C ⦋2⦌) :
    ComponentCategory.arrowOf C (representative σ 0 1 (by decide)) ≫
        ComponentCategory.arrowOf C (representative σ 1 2 (by decide)) =
      ComponentCategory.arrowOf C (representative σ 0 2 (by decide)) := by
  have hL : NativeTriangleCell.left σ = representative σ 0 1 (by decide) :=
    congrArg (fun p => (σ.map NativeTriangleCell.p0 NativeTriangleCell.p1).app (op ⦋0⦌)
      (ComposableArrows.mk₀ (C := SimplicialThickening.Path
        (ULift.up.{u} (0 : Fin 3)) (ULift.up.{u} (1 : Fin 3))) p)) leftPath_eq
  have hR : NativeTriangleCell.right σ = representative σ 1 2 (by decide) :=
    congrArg (fun p => (σ.map NativeTriangleCell.p1 NativeTriangleCell.p2).app (op ⦋0⦌)
      (ComposableArrows.mk₀ (C := SimplicialThickening.Path
        (ULift.up.{u} (1 : Fin 3)) (ULift.up.{u} (2 : Fin 3))) p)) rightPath_eq
  have hD : NativeTriangleCell.direct σ = representative σ 0 2 (by decide) := rfl
  have h := SSet.π₀.sound (NativeTriangleCell.compositionEdge σ)
  rw [hL, hR, hD] at h
  exact (ComponentCategory.arrowOf_composition C _ _).trans h.symm

end CategoryTheory.CoherentRealization.ComponentSimplexReadback

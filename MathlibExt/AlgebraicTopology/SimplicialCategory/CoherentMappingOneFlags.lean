/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentEdgeVertexEvaluation

/-!
# Actual first-dimensional original mapping flag relations

The zero flag is the literal two-endpoint path in every finite height.
The top flag in height one is the actual union of the two original
adjacent endpoint paths. A supplied original right-mapping one-simplex
has the genuine source identity on its whole front edge.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.MappingOneFlags
open SimplicialEnrichment RightMappingSimplex AdjacentHom PathMaximumFlags PathLastMaximum
open HomFlagEvaluation HomMappingCells EdgeVertexEvaluation

/-- At any original finite height, the zero-front flag is precisely the literal source-to-last endpoint path. -/
theorem zero_flag {n : ℕ} : flag.{u} (0 : Fin (n + 1)) =
    endpointPath (ULift.up.{u} (0 : Fin (n + 2))) (ULift.up (Fin.last (n + 1))) (Fin.zero_le _) := by
  apply SimplicialThickening.Path.ext
  ext k
  change (k ≤ ULift.up.{u} (0 : Fin (n + 2)) ∨ k = ULift.up (Fin.last (n + 1))) ↔
    (k = ULift.up (0 : Fin (n + 2)) ∨ k = ULift.up (Fin.last (n + 1)))
  constructor
  · rintro (hk | hk)
    · exact Or.inl (le_antisymm hk (show ULift.up.{u} (0 : Fin (n + 2)) ≤ k from Fin.zero_le k.down))
    · exact Or.inr hk
  · rintro (rfl | hk)
    · exact Or.inl le_rfl
    · exact Or.inr hk

/-- The original top flag through the middle vertex is exactly the whole union of the two actual adjacent
  endpoint paths. -/
theorem one_flag : compose (0 : Fin 2) 1
    (endpointPath (ULift.up.{u} (0 : Fin 3)) (ULift.up (1 : Fin 3)) (by decide))
    (endpointPath (ULift.up.{u} (1 : Fin 3)) (ULift.up (2 : Fin 3)) (by decide)) = flag.{u} (1 : Fin 2) := by
  apply SimplicialThickening.Path.ext
  ext k
  cases k with | up k =>
    fin_cases k <;> simp [compose, endpointPath, flag, SimplicialThickening.compFunctor, SimplicialThickening.comp_I]

/-- An actual enriched functor preserves the entire original two-factor composition under its three supplied
  endpoint object equalities. -/
theorem mapped_composition {A C : Carrier.{u}} (F : A ⟶ C) (a b c : A) {x y z : C}
    (hx : F.obj a = x) (hy : F.obj b = y) (hz : F.obj c = z) :
    eComp SSet.{u} a b c ≫ (F.map a c ≫ EqualityTransport.hom hx hz) =
      ((F.map a b ≫ EqualityTransport.hom hx hy) ⊗ₘ (F.map b c ≫ EqualityTransport.hom hy hz)) ≫ eComp SSet.{u} x y z :=
  EqualityTransport.composition_retarget a b c hx hy hz _ _ _ (F.map_comp a b c)

/-- The original front adjacent endpoint path is mapped by the last-face operator to that same literal original path. -/
theorem front_path_image :
    ((coherentSimplexMap (SimplexCategory.δ (2 : Fin 3))).map
      (.mk (ULift.up.{u} (0 : Fin 2))) (.mk (ULift.up.{u} (1 : Fin 2)))).app (op ⦋0⦌)
        (ComposableArrows.mk₀ (endpointPath (ULift.up.{u} (0 : Fin 2)) (ULift.up (1 : Fin 2)) (by decide))) =
      ComposableArrows.mk₀ (endpointPath (ULift.up.{u} (0 : Fin 3)) (ULift.up (1 : Fin 3)) (by decide)) := by
  change (nerveMap (SimplicialThickening.functorMap (SimplexCategory.δ (2 : Fin 3)).toOrderHom.uliftMap
    (SimplicialThickening.mk (ULift.up.{u} (0 : Fin 2))) (SimplicialThickening.mk (ULift.up.{u} (1 : Fin
      2))))).app (op ⦋0⦌)
      (ComposableArrows.mk₀ (endpointPath (ULift.up.{u} (0 : Fin 2)) (ULift.up (1 : Fin 2)) (by decide))) = _
  apply ComposableArrows.ext₀
  apply SimplicialThickening.Path.ext
  change (SimplexCategory.δ (2 : Fin 3)).toOrderHom.uliftMap '' {ULift.up.{u} (0 : Fin 2), ULift.up (1 : Fin 2)} =
    {ULift.up.{u} (0 : Fin 3), ULift.up (1 : Fin 3)}
  rw [Set.image_insert_eq, Set.image_singleton]
  rfl

/-- A supplied actual coherent right-mapping one-simplex maps its original front endpoint path to the same
  genuine source identity. -/
theorem front_identity (C : Carrier.{u}) (x y : C)
    (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (HomSimplexEndpoints.vertex x)
      (HomSimplexEndpoints.vertex y)) _⦋1⦌) :
    (EqualityTransport.hom (front_obj x y σ (0 : Fin 2)) (front_obj x y σ (1 : Fin 2))).app (op ⦋0⦌)
      (((toEnriched x y σ).map (.mk (ULift.up (0 : Fin 3))) (.mk (ULift.up (1 : Fin 3)))).app (op ⦋0⦌)
        (ComposableArrows.mk₀ (endpointPath (ULift.up.{u} (0 : Fin 3)) (ULift.up (1 : Fin 3)) (by decide)))) =
      (eId SSet.{u} x).app (op ⦋0⦌) PUnit.unit := by
  let F := coherentSimplexMap (SimplexCategory.δ (2 : Fin 3)) ≫ toEnriched x y σ
  let T := constantSimplex C ⦋1⦌ x
  let A : FixedSimplex x x (n := 0) := ⟨F, front_obj x y σ (0 : Fin 2), front_obj x y σ (1 : Fin 2)⟩
  let B : FixedSimplex x x (n := 0) := ⟨T, rfl, rfl⟩
  have hA : A = B := Subtype.ext (front x y σ)
  have hR := congrArg (FixedEdgeReadback.readVertex x x) hA
  have hConst : FixedEdgeReadback.readVertex x x B = (eId SSet.{u} x).app (op ⦋0⦌) PUnit.unit := rfl
  have hRaw := read_fixed x x A
  have hPath := front_path_image.{u}
  have hLeft : FixedEdgeReadback.readVertex x x A =
      (EqualityTransport.hom (front_obj x y σ (0 : Fin 2)) (front_obj x y σ (1 : Fin 2))).app (op ⦋0⦌)
        (((toEnriched x y σ).map (.mk (ULift.up (0 : Fin 3))) (.mk (ULift.up (1 : Fin 3)))).app (op ⦋0⦌)
          (ComposableArrows.mk₀ (endpointPath (ULift.up.{u} (0 : Fin 3)) (ULift.up (1 : Fin 3)) (by decide)))) :=
    hRaw.trans (congrArg (fun p => (EqualityTransport.hom A.2.1 A.2.2).app (op ⦋0⦌)
      (((toEnriched x y σ).map (.mk (ULift.up (0 : Fin 3))) (.mk (ULift.up (1 : Fin 3)))).app (op ⦋0⦌) p)) hPath)
  exact hLeft.symm.trans (hR.trans hConst)

end CategoryTheory.CoherentRealization.MappingOneFlags

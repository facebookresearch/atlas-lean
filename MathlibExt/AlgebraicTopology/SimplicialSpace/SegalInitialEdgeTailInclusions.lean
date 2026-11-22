/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalInitialEdgeTailCover

/-!
# Whole original edge, tail and shared-vertex maps into the Segal path cover

The actual standard face and interval isomorphisms retain their complete
original maps into the same cover. Both shared-vertex equations use the
original endpoint faces. These maps give the native pullback comparison
of path rows, with no replacement of original simplex operators.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SSet.Rezk.InitialEdgeTail

/-- The whole original tail simplex enters its same original path cover. -/
def tailInclusion (n : ℕ) : (Δ[n] : SSet.{u}) ⟶ (initialIntervalCover (n + 1) : SSet.{u}) :=
  (tailIso n).hom ≫ Subcomplex.homOfLE (by rw [← union_cover]; exact le_sup_left)

/-- The whole original leading edge enters its same original path cover. -/
def edgeInclusion (n : ℕ) : (Δ[1] : SSet.{u}) ⟶ (initialIntervalCover (n + 1) : SSet.{u}) :=
  (edgeIso n).hom ≫ Subcomplex.homOfLE (by rw [← union_cover]; exact le_sup_right)

/-- The original shared vertex enters the whole tail simplex at its original first vertex. -/
def vertexToTail (n : ℕ) : (Δ[0] : SSet.{u}) ⟶ Δ[n] :=
  SSet.stdSimplex.map (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk n) 0)

/-- The whole tail inclusion retains the original first face in the same ambient simplex. -/
theorem tailInclusion_ambient (n : ℕ) :
    tailInclusion.{u} n ≫ (initialIntervalCover (n + 1)).ι =
      SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin (n + 2))) := by
  rw [tailInclusion, Category.assoc]
  exact tailIso_inclusion n

/-- The whole edge inclusion retains the original adjacent first edge in the same ambient simplex. -/
theorem edgeInclusion_ambient (n : ℕ) :
    edgeInclusion.{u} n ≫ (initialIntervalCover (n + 1)).ι =
      SSet.stdSimplex.map (SimplexCategory.mkOfSucc (0 : Fin (n + 1))) := by
  rw [edgeInclusion, Category.assoc]
  exact edgeIso_inclusion n

/-- Both original shared-vertex maps are the identical vertex in the whole original cover. -/
theorem sharedVertex (n : ℕ) :
    vertexToTail.{u} n ≫ tailInclusion n = SSet.stdSimplex.δ (0 : Fin 2) ≫ edgeInclusion n := by
  apply (cancel_mono (initialIntervalCover.{u} (n + 1)).ι).mp
  rw [Category.assoc, tailInclusion_ambient, Category.assoc, edgeInclusion_ambient]
  unfold vertexToTail
  change SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _ =
    SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) ≫ SSet.stdSimplex.map _
  rw [← SSet.stdSimplex.map_comp, ← SSet.stdSimplex.map_comp]
  apply congrArg SSet.stdSimplex.map
  ext i
  fin_cases i
  rfl

/-- The whole shared vertex retains its original first-vertex map in the complete tail face. -/
theorem vertex_tail_equation (n : ℕ) :
    (vertexIso.{u} n).hom ≫ Subcomplex.homOfLE
        (show vertex.{u} n ≤ tail n from by rw [← intersection_vertex]; exact inf_le_left) =
      vertexToTail n ≫ (tailIso n).hom := by
  apply (cancel_mono (tail.{u} n).ι).mp
  simp only [Category.assoc]
  rw [tailIso_inclusion]
  change (vertexIso n).hom ≫ (vertex n).ι = _
  rw [vertexIso_inclusion]
  unfold vertexToTail
  rw [← SSet.stdSimplex.map_comp]
  apply congrArg SSet.stdSimplex.map
  ext i
  fin_cases i
  rfl

/-- The whole shared vertex retains its original target endpoint in the complete initial edge. -/
theorem vertex_edge_equation (n : ℕ) :
    (vertexIso.{u} n).hom ≫ Subcomplex.homOfLE
        (show vertex.{u} n ≤ edge n from by rw [← intersection_vertex]; exact inf_le_right) =
      SSet.stdSimplex.δ (0 : Fin 2) ≫ (edgeIso n).hom := by
  apply (cancel_mono (edge.{u} n).ι).mp
  simp only [Category.assoc]
  rw [edgeIso_inclusion]
  change (vertexIso n).hom ≫ (vertex n).ι = _
  rw [vertexIso_inclusion]
  change SSet.stdSimplex.map _ = SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _
  rw [← SSet.stdSimplex.map_comp]
  apply congrArg SSet.stdSimplex.map
  ext i
  fin_cases i
  rfl

/-- The actual whole initial edge and full tail form the original cover pushout over their original vertex. -/
theorem simplex_isPushout (n : ℕ) :
    IsPushout (vertexToTail.{u} n) (SSet.stdSimplex.δ (0 : Fin 2))
      (tailInclusion n) (edgeInclusion n) :=
  (isPushout.{u} n).of_iso' (vertexIso n) (tailIso n) (edgeIso n)
    (Iso.refl (initialIntervalCover (n + 1) : SSet.{u}))
    (vertex_tail_equation n) (vertex_edge_equation n) (by simp only [Iso.refl_hom, Category.comp_id]; rfl)
    (by simp only [Iso.refl_hom, Category.comp_id]; rfl)

end SSet.Rezk.InitialEdgeTail

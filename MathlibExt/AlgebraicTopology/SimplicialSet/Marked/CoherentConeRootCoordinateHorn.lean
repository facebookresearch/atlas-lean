/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootCoordinateFaces
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCoordinateBoundary

/-!
# The same original root-coordinate horn in the complete original prism

Retain every original upper coordinate face and every original lower
coordinate face except the one omitted original lower coordinate. The
SAME whole original coface/insertion prism pulls this entire original
subcomplex back to its original upper endpoint and smaller-root coordinate
boundary union, at every vertex of every whole original simplex.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- The actual original root horn retains all upper coordinate faces and all lower coordinate faces except the
single original omitted lower coordinate. -/
def coneRootCoordinateHorn {n : ℕ} (j : Fin (n + 2)) :
    (coneWeight (⊥ : Vertex.{u} (n + 1))).toSSet.Subcomplex :=
  ⨆ k : Sum {k : Vertex.{u} (n + 1) // ⊥ < k}
      {k : Vertex.{u} (n + 1) // ⊥ < k ∧ k ≠ ULift.up j},
    match k with
    | .inl k => coneCoordinateFace ⊥ k.val true
    | .inr k => coneCoordinateFace ⊥ k.val false

/-- The actual whole original horn word has one unchanged upper coordinate or one unchanged nonomitted lower
coordinate. -/
theorem mem_coneRootCoordinateHorn_iff {n : ℕ} (j : Fin (n + 2))
    (q : SimplexCategoryᵒᵖ) (a : (coneWeight (⊥ : Vertex.{u} (n + 1))).toSSet.obj q) :
    a ∈ (coneRootCoordinateHorn j).obj q ↔
      (∃ k : {k : Vertex.{u} (n + 1) // ⊥ < k}, ∀ t, k.val ∈ (a.obj t).vertices) ∨
        (∃ k : {k : Vertex.{u} (n + 1) // ⊥ < k ∧ k ≠ ULift.up j}, ∀ t, k.val ∉ (a.obj t).vertices) := by
  simp only [coneRootCoordinateHorn, Subfunctor.iSup_obj, Set.mem_iUnion, Sum.exists,
    coneCoordinateFace, Bool.false_eq_true, iff_false, iff_true]
  rfl

/-- The whole actual original root-coordinate horn inherits exactly the SAME original larger-root maximum marking. -/
def coneRootCoordinateHornMarked {n : ℕ} (j : Fin (n + 2)) : Marked.{u} :=
  comap (coneWeight (⊥ : Vertex.{u} (n + 1))) (coneRootCoordinateHorn j).ι

/-- The original complete horn inclusion retains every original simplex and exactly its inherited original marking. -/
def coneRootCoordinateHornMap {n : ℕ} (j : Fin (n + 2)) :
    coneRootCoordinateHornMarked j ⟶ coneWeight (⊥ : Vertex.{u} (n + 1)) :=
  comapHom (coneWeight (⊥ : Vertex.{u} (n + 1))) (coneRootCoordinateHorn j).ι

/-- The actual original marked root-coordinate horn is monic on its unchanged original simplicial carrier. -/
instance {n : ℕ} (j : Fin (n + 2)) : Mono (coneRootCoordinateHornMap.{u} j) :=
  (mono_iff_underlying _).mpr (inferInstance : Mono (coneRootCoordinateHorn.{u} j).ι)

/-- The SAME full original coface/insertion prism identifies the entire original root-coordinate horn with its
original upper endpoint and whole smaller-root coordinate-boundary union. -/
theorem coneRootCoordinateHorn_preimage {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    (coneRootCoordinateHorn j).preimage (coneRootCoordinateWholeMap j hj) =
      Subcomplex.unionProd (horn.{u} 1 (Fin.last 1)) (coneCoordinateBoundary (⊥ : Vertex.{u} n)) := by
  classical
  ext q z
  change (coneRootCoordinateWholeMap j hj).app q z ∈ (coneRootCoordinateHorn j).obj q ↔
    z ∈ (Subcomplex.unionProd (horn.{u} 1 (Fin.last 1)) (coneCoordinateBoundary (⊥ : Vertex.{u} n))).obj q
  constructor
  · intro h
    apply (Subcomplex.mem_unionProd_iff _ _ z).mpr
    rcases (mem_coneRootCoordinateHorn_iff j q ((coneRootCoordinateWholeMap j hj).app q z)).mp h with
      ⟨k, hk⟩ | ⟨k, hk⟩
    · by_cases heq : k.val = ULift.up j
      · right
        apply (coneRootCoordinate_upper_endpoint_iff q z.1).mpr
        intro t
        exact (coneRootCoordinateWholeMap_mem_self j hj q z t).mp (heq ▸ hk t)
      · left
        obtain ⟨l, hl⟩ := (mem_coneCofaceEmbedding_range j k.val).mpr heq
        have hlpos : (⊥ : Vertex.{u} n) < l := by
          apply (coneCofaceEmbedding j).lt_iff_lt.mp
          rw [coneCofaceEmbedding_root j hj, hl]
          exact k.property
        apply (mem_coneCoordinateBoundary_iff (⊥ : Vertex.{u} n) z.2).mpr
        refine ⟨⟨l, hlpos⟩, true, fun t => ?_⟩
        constructor
        · intro _
          rfl
        · intro _
          exact (coneRootCoordinateWholeMap_mem_image j hj q z t l).mp (hl.symm ▸ hk t)
    · left
      obtain ⟨l, hl⟩ := (mem_coneCofaceEmbedding_range j k.val).mpr k.property.2
      have hlpos : (⊥ : Vertex.{u} n) < l := by
        apply (coneCofaceEmbedding j).lt_iff_lt.mp
        rw [coneCofaceEmbedding_root j hj, hl]
        exact k.property.1
      apply (mem_coneCoordinateBoundary_iff (⊥ : Vertex.{u} n) z.2).mpr
      refine ⟨⟨l, hlpos⟩, false, fun t => ?_⟩
      constructor
      · intro ht
        have hmem : k.val ∈ (((coneRootCoordinateWholeMap j hj).app q z).obj t).vertices :=
          hl ▸ (coneRootCoordinateWholeMap_mem_image j hj q z t l).mpr ht
        exact (hk t hmem).elim
      · intro h
        cases h
  · intro h
    apply (mem_coneRootCoordinateHorn_iff j q ((coneRootCoordinateWholeMap j hj).app q z)).mpr
    rcases (Subcomplex.mem_unionProd_iff _ _ z).mp h with hb | hu
    · obtain ⟨l, ε, hε⟩ := (mem_coneCoordinateBoundary_iff (⊥ : Vertex.{u} n) z.2).mp hb
      have hpos : (⊥ : Vertex.{u} (n + 1)) < coneCofaceEmbedding j l.val := by
        rw [← coneCofaceEmbedding_root j hj]
        exact (coneCofaceEmbedding j).strictMono l.property
      have hne : coneCofaceEmbedding j l.val ≠ ULift.up j :=
        (mem_coneCofaceEmbedding_range j _).mp ⟨l.val, rfl⟩
      cases ε
      · right
        refine ⟨⟨coneCofaceEmbedding j l.val, hpos, hne⟩, fun t ht => ?_⟩
        have hlt : l.val ∈ (z.2.obj t).vertices := (coneRootCoordinateWholeMap_mem_image j hj q z t l.val).mp ht
        have hbad : false = true := (hε t).mp hlt
        cases hbad
      · left
        refine ⟨⟨coneCofaceEmbedding j l.val, hpos⟩, fun t => ?_⟩
        exact (coneRootCoordinateWholeMap_mem_image j hj q z t l.val).mpr ((hε t).mpr rfl)
    · left
      refine ⟨⟨ULift.up j, show (⊥ : Vertex.{u} (n + 1)) < ULift.up j from hj⟩, fun t => ?_⟩
      exact (coneRootCoordinateWholeMap_mem_self j hj q z t).mpr
        ((coneRootCoordinate_upper_endpoint_iff q z.1).mp hu t)

end SSet.Marked.CoherentWeight

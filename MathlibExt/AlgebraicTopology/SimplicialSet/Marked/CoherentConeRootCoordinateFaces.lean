/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootCoordinatePrism
import Mathlib.AlgebraicTopology.SimplicialSet.Horn

/-!
# Every original coordinate face in the same whole root prism

The original omitted coordinate reads exactly the original upper
interval layer. Every remaining original coordinate reads exactly its
same whole coface preimage. These statements hold at every vertex of
every original scalar word. The native upper interval horn is exactly
the constant original upper-coordinate simplex.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

private theorem coordinateInterval_bot_ne_top : (⊥ : Vertex.{u} 1) ≠ ⊤ := by decide

/-- The actual original membership coordinate is upper precisely when the same original coordinate belongs to the
whole original subset. -/
theorem coneRootCoordinateMembership_eq_top_iff {n : ℕ} (j : Fin (n + 2))
    (a : ConeSubset (⊥ : Vertex.{u} (n + 1))) :
    coneRootCoordinateMembership j a = (⊤ : Vertex.{u} 1) ↔ ULift.up j ∈ a.vertices := by
  by_cases ha : ULift.up j ∈ a.vertices
  · rw [coneRootCoordinateMembership, ite_eq_left ha]
    exact ⟨fun _ => ha, fun _ => rfl⟩
  · rw [coneRootCoordinateMembership, ite_eq_right ha]
    constructor
    · intro h
      exact (coordinateInterval_bot_ne_top h).elim
    · intro h
      exact (ha h).elim

/-- Every actual original smaller coordinate belongs to the full original preimage exactly when its unchanged
original coface image belongs to the same original larger subset. -/
theorem coneRootCofacePreimage_mem_iff {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (a : ConeSubset (⊥ : Vertex.{u} (n + 1))) (k : Vertex.{u} n) :
    k ∈ (coneRootCofacePreimage j hj a).vertices ↔ coneCofaceEmbedding j k ∈ a.vertices := by
  simp only [coneRootCofacePreimage, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The same actual original reconstructed omitted coordinate is present precisely in the original upper interval
layer. -/
theorem coneRootCoordinateRebuild_mem_self {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (z : Vertex.{u} 1 × ConeSubset (⊥ : Vertex.{u} n)) :
    ULift.up j ∈ (coneRootCoordinateRebuild j hj z).vertices ↔ z.1 = ⊤ := by
  have h : coneRootCoordinateMembership j (coneRootCoordinateRebuild j hj z) = z.1 :=
    congrArg Prod.fst (coneRootCoordinateSplit_rebuild j hj z)
  exact (coneRootCoordinateMembership_eq_top_iff j _).symm.trans
    (congrArg (fun t : Vertex.{u} 1 => t = ⊤) h).to_iff

/-- Every remaining original coordinate of the whole reconstructed larger subset reads exactly its same original
smaller-root coordinate. -/
theorem coneRootCoordinateRebuild_mem_image {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (z : Vertex.{u} 1 × ConeSubset (⊥ : Vertex.{u} n)) (k : Vertex.{u} n) :
    coneCofaceEmbedding j k ∈ (coneRootCoordinateRebuild j hj z).vertices ↔ k ∈ z.2.vertices := by
  have h : coneRootCofacePreimage j hj (coneRootCoordinateRebuild j hj z) = z.2 :=
    congrArg Prod.snd (coneRootCoordinateSplit_rebuild j hj z)
  exact (coneRootCofacePreimage_mem_iff j hj _ k).symm.trans
    (congrArg (fun a : ConeSubset (⊥ : Vertex.{u} n) => k ∈ a.vertices) h).to_iff

/-- Every whole original prism simplex retains the literal omitted-coordinate membership at every unchanged original
scalar vertex. -/
theorem coneRootCoordinateWholeMap_mem_self {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (q : SimplexCategoryᵒᵖ)
    (z : ((Δ[1] : SSet.{u}) ⊗ (coneWeight (⊥ : Vertex.{u} n)).toSSet).obj q)
    (t : Fin (q.unop.len + 1)) :
    ULift.up j ∈ (((coneRootCoordinateWholeMap j hj).app q z).obj t).vertices ↔
      ((stdSimplex.isoNerve 1).hom.app q z.1).obj t = (⊤ : Vertex.{u} 1) := by
  rw [coneRootCoordinateWholeMap_obj]
  exact coneRootCoordinateRebuild_mem_self j hj _

/-- Every whole original prism simplex retains each remaining original coordinate at every unchanged original scalar
vertex. -/
theorem coneRootCoordinateWholeMap_mem_image {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (q : SimplexCategoryᵒᵖ)
    (z : ((Δ[1] : SSet.{u}) ⊗ (coneWeight (⊥ : Vertex.{u} n)).toSSet).obj q)
    (t : Fin (q.unop.len + 1)) (k : Vertex.{u} n) :
    coneCofaceEmbedding j k ∈ (((coneRootCoordinateWholeMap j hj).app q z).obj t).vertices ↔
      k ∈ (z.2.obj t).vertices := by
  rw [coneRootCoordinateWholeMap_obj]
  exact coneRootCoordinateRebuild_mem_image j hj _ k

/-- The native original upper interval horn contains exactly the complete original interval words whose every
original vertex is upper. -/
theorem coneRootCoordinate_upper_endpoint_iff (q : SimplexCategoryᵒᵖ) (e : (Δ[1] : SSet.{u}).obj q) :
    e ∈ (horn.{u} 1 (Fin.last 1)).obj q ↔
      ∀ t : Fin (q.unop.len + 1), ((stdSimplex.isoNerve 1).hom.app q e).obj t = (⊤ : Vertex.{u} 1) := by
  rw [mem_horn_iff]
  constructor
  · intro he t
    have h₀ : (0 : Fin 2) ∉ Set.range (stdSimplex.asOrderHom e) := by
      intro h
      apply he
      apply Set.eq_univ_of_forall
      intro k
      fin_cases k
      · exact Or.inl h
      · exact Or.inr rfl
    have ht : stdSimplex.asOrderHom e t ≠ (0 : Fin 2) := fun h => h₀ ⟨t, h⟩
    apply ULift.ext
    change stdSimplex.asOrderHom e t = Fin.last 1
    apply Fin.ext
    have hne : (stdSimplex.asOrderHom e t).val ≠ 0 := fun h => ht (Fin.ext h)
    have hlt := (stdSimplex.asOrderHom e t).isLt
    change (stdSimplex.asOrderHom e t).val = 1
    omega
  · intro he h
    have h₀ : (0 : Fin 2) ∈ Set.range (stdSimplex.asOrderHom e) ∪ {Fin.last 1} :=
      h.symm ▸ Set.mem_univ _
    rcases h₀ with ⟨t, ht⟩ | ht
    · have he' : stdSimplex.asOrderHom e t = Fin.last 1 := congrArg ULift.down (he t)
      exact (by decide : (0 : Fin 2) ≠ Fin.last 1) (ht.symm.trans he')
    · exact (by decide : (0 : Fin 2) ≠ Fin.last 1) ht

end SSet.Marked.CoherentWeight

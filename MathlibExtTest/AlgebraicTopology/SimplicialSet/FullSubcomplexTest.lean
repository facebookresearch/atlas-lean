/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FullSubcomplex

@[expose] public section

/-!
# Full-subcomplex client test

Downstream client for `SSet.Subcomplex.full`, exercised on `Δ[1]`. The
identity edge of `Δ[1]` lies in the full subcomplex on both vertices but
not in the full subcomplex on the single vertex `0`, while the constant
edge at `0` does lie in the latter: this distinguishes the genuine
"all vertices" condition from a first-vertex-only condition. The test
also exercises the vertex-set characterization, monotonicity, the
`0`-simplex equivalence, preimage/image functoriality and the induced
map `mapFull` along the constant map at `0`, factorization of
simplices through full subcomplexes, and the inner fibration
instance for the inclusion.
-/

set_option autoImplicit false

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.FullSubcomplexTest

/-- The vertices of `Δ[1]`. -/
def vertex (i : Fin 2) : (Δ[1] : SSet.{0}) _⦋0⦌ :=
  SSet.stdSimplex.obj₀Equiv.symm i

/-- The identity edge of `Δ[1]`, with vertices `0` and `1`. -/
def idEdge : (Δ[1] : SSet.{0}) _⦋1⦌ :=
  SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)

/-- The constant edge of `Δ[1]` at vertex `0`. -/
def constEdge : (Δ[1] : SSet.{0}) _⦋1⦌ :=
  SSet.stdSimplex.const 1 0 (op ⦋1⦌)

lemma obj₀Equiv_vertex (i : Fin 2) :
    SSet.stdSimplex.obj₀Equiv (vertex i) = i :=
  Equiv.apply_symm_apply _ _

lemma vertex_zero_ne_one : vertex 0 ≠ vertex 1 := by
  intro h
  have h01 := congrArg SSet.stdSimplex.obj₀Equiv h
  rw [obj₀Equiv_vertex, obj₀Equiv_vertex] at h01
  exact (by decide : (0 : Fin 2) ≠ 1) h01

lemma vertex_idEdge (i : Fin 2) :
    (Δ[1] : SSet.{0}).map (SimplexCategory.const ⦋0⦌ ⦋1⦌ i).op idEdge =
      vertex i := by
  ext j
  fin_cases j
  rfl

lemma vertex_constEdge (i : Fin 2) :
    (Δ[1] : SSet.{0}).map (SimplexCategory.const ⦋0⦌ ⦋1⦌ i).op constEdge =
      vertex 0 := by
  ext j
  fin_cases j
  rfl

/-- The constant edge at `0` lies in the full subcomplex on `{0}`. -/
lemma constEdge_mem_full_singleton :
    constEdge ∈ (SSet.Subcomplex.full {vertex 0}).obj (op ⦋1⦌) :=
  SSet.Subcomplex.mem_full_obj_iff_vertices.mpr (fun i ↦ by
    simp [vertex_constEdge i])

/-- Both faces of the constant edge lie in the full subcomplex on
`{0}`, by stability under simplicial operators. -/
lemma face_constEdge_mem_full_singleton (i : Fin 2) :
    (Δ[1] : SSet.{0}).δ i constEdge ∈
      (SSet.Subcomplex.full {vertex 0}).obj (op ⦋0⦌) :=
  SSet.Subcomplex.map_mem_full_obj _ constEdge_mem_full_singleton

/-- The identity edge does not lie in the full subcomplex on `{0}`,
since its vertex `1` is not in `{0}`. -/
lemma idEdge_notMem_full_singleton :
    idEdge ∉ (SSet.Subcomplex.full {vertex 0}).obj (op ⦋1⦌) := by
  intro h
  have h1 := SSet.Subcomplex.mem_full_obj_iff_vertices.mp h 1
  rw [vertex_idEdge] at h1
  have h10 : vertex 1 = vertex 0 := h1
  exact vertex_zero_ne_one h10.symm

/-- The identity edge lies in the full subcomplex on both vertices. -/
lemma idEdge_mem_full_pair :
    idEdge ∈ (SSet.Subcomplex.full {vertex 0, vertex 1}).obj (op ⦋1⦌) :=
  SSet.Subcomplex.mem_full_obj_iff_vertices.mpr (fun i ↦ by
    fin_cases i <;> simp [vertex_idEdge])

/-- The full subcomplex on all vertices of `Δ[1]` is everything. -/
theorem full_univ_delta_one :
    SSet.Subcomplex.full (Set.univ : Set ((Δ[1] : SSet.{0}) _⦋0⦌)) = ⊤ :=
  SSet.Subcomplex.full_univ

/-- The full subcomplex on no vertices of `Δ[1]` is empty. -/
theorem full_empty_delta_one :
    SSet.Subcomplex.full (∅ : Set ((Δ[1] : SSet.{0}) _⦋0⦌)) = ⊥ :=
  SSet.Subcomplex.full_empty

/-- The vertex set of the full subcomplex on `{0}` is `{0}`. -/
lemma full_singleton_obj_zero :
    (SSet.Subcomplex.full {vertex 0}).obj (op ⦋0⦌) = {vertex 0} :=
  SSet.Subcomplex.full_obj_zero _

/-- Vertex `1` is not a `0`-simplex of the full subcomplex on `{0}`. -/
lemma vertex_one_notMem_full_singleton :
    vertex 1 ∉ (SSet.Subcomplex.full {vertex 0}).obj (op ⦋0⦌) := by
  simp only [SSet.Subcomplex.mem_full_obj_zero_iff, Set.mem_singleton_iff]
  exact fun h ↦ vertex_zero_ne_one h.symm

/-- The element of `full {0}` corresponding to the chosen vertex. -/
def zeroVertexFull :
    ((SSet.Subcomplex.full {vertex 0} : (Δ[1] : SSet.{0}).Subcomplex) :
      SSet.{0}) _⦋0⦌ :=
  (SSet.Subcomplex.full.obj₀Equiv {vertex 0}).symm ⟨vertex 0, rfl⟩

lemma zeroVertexFull_val : zeroVertexFull.1 = vertex 0 :=
  SSet.Subcomplex.full_obj₀Equiv_symm_apply_val _ _

lemma objZeroEquiv_zeroVertexFull_val :
    (SSet.Subcomplex.full.obj₀Equiv {vertex 0} zeroVertexFull).1 = vertex 0 := by
  simp [zeroVertexFull]

/-- Monotonicity: the full subcomplex on `{0}` is contained in the one
on both vertices (and the containment is strict, by `idEdge` above). -/
lemma full_singleton_le_pair :
    SSet.Subcomplex.full {vertex 0} ≤
      SSet.Subcomplex.full {vertex 0, vertex 1} :=
  SSet.Subcomplex.full_le_full (by
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    simp [hx])

lemma full_singleton_le_pair_monotone :
    SSet.Subcomplex.full {vertex 0} ≤
      SSet.Subcomplex.full {vertex 0, vertex 1} :=
  SSet.Subcomplex.monotone_full (by
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    simp [hx])

/-- The subcomplex generated by vertex `0` is contained in `full {0}`,
checked through the largest-subcomplex characterization. -/
lemma ofSimplex_vertex_zero_le_full_singleton :
    SSet.Subcomplex.ofSimplex (vertex 0) ≤ SSet.Subcomplex.full {vertex 0} := by
  rw [SSet.Subcomplex.le_full_iff]
  intro y hy
  rw [SSet.Subcomplex.mem_ofSimplex_obj_iff] at hy
  obtain ⟨f, hf⟩ := hy
  have hmap : (Δ[1] : SSet.{0}).map f.op (vertex 0) = vertex 0 := by
    ext j
    fin_cases j
    rfl
  rw [hmap] at hf
  rw [← hf]
  exact Set.mem_singleton _

/-- The constant map `Δ[1] ⟶ Δ[1]` at vertex `0`. -/
def constZeroMap : (Δ[1] : SSet.{0}) ⟶ Δ[1] := SSet.const (vertex 0)

lemma constZeroMap_app_zero (x : (Δ[1] : SSet.{0}) _⦋0⦌) :
    constZeroMap.app (op ⦋0⦌) x = vertex 0 := by
  simp [constZeroMap]

/-- Pulling `full {0}` back along the constant map at `0` gives all of
`Δ[1]`, since every vertex maps to `0`. -/
theorem preimage_full_singleton_constZeroMap :
    (SSet.Subcomplex.full {vertex 0}).preimage constZeroMap = ⊤ := by
  rw [SSet.Subcomplex.full_preimage]
  have hset : constZeroMap.app (op ⦋0⦌) ⁻¹' ({vertex 0} : Set _) = Set.univ := by
    ext x
    simp [constZeroMap_app_zero]
  rw [hset]
  exact SSet.Subcomplex.full_univ

/-- The image of `full {1}` along the constant map at `0` is contained
in `full {0}`. -/
lemma image_full_singleton_one_constZeroMap_le :
    (SSet.Subcomplex.full {vertex 1}).image constZeroMap ≤
      SSet.Subcomplex.full {vertex 0} := by
  have h := SSet.Subcomplex.image_full_le constZeroMap {vertex 1}
  have hset : constZeroMap.app (op ⦋0⦌) '' ({vertex 1} : Set _) = {vertex 0} := by
    simp [constZeroMap_app_zero]
  rwa [hset] at h

/-- The map on full subcomplexes induced by the constant map at `0`. -/
def inducedConstZero :
    ((SSet.Subcomplex.full {vertex 1} : (Δ[1] : SSet.{0}).Subcomplex) :
        SSet.{0}) ⟶
      ((SSet.Subcomplex.full {vertex 0} : (Δ[1] : SSet.{0}).Subcomplex) :
        SSet.{0}) :=
  SSet.Subcomplex.mapFull constZeroMap (fun hx ↦ by
    simp [constZeroMap_app_zero])

lemma inducedConstZero_ι :
    inducedConstZero ≫ (SSet.Subcomplex.full {vertex 0}).ι =
      (SSet.Subcomplex.full {vertex 1}).ι ≫ constZeroMap := by
  unfold inducedConstZero
  exact SSet.Subcomplex.mapFull_ι constZeroMap _

/-- The inclusion of `full {0}` in `Δ[1]` is an inner fibration. -/
theorem full_singleton_ι_innerFibration :
    SSet.InnerFibration (SSet.Subcomplex.full {vertex 0}).ι :=
  inferInstance

theorem full_singleton_mem_innerFibrations :
    SSet.innerFibrations (SSet.Subcomplex.full {vertex 0}).ι :=
  SSet.mem_innerFibrations _

/-- Unpacked: the inclusion lifts against the inner horn `Λ[2, 1]`. -/
theorem full_singleton_lifts_inner_horn :
    HasLiftingProperty Λ[2, (1 : Fin 3)].ι
      (SSet.Subcomplex.full {vertex 0}).ι :=
  SSet.Subcomplex.hasLiftingProperty_horn_full_ι _ _

/-- Every simplex factors through the full subcomplex on all
vertices. -/
example {X : SSet.{u}} {n : ℕ} (σ : Δ[n] ⟶ X) :
    ∃ σ' : Δ[n] ⟶ (SSet.Subcomplex.full Set.univ : SSet.{u}),
      σ' ≫ (SSet.Subcomplex.full Set.univ).ι = σ :=
  SSet.Subcomplex.exists_factorThru_full_ι σ (fun _ => Set.mem_univ _)

/-- Factorization through a full subcomplex is determined by the
vertices of the simplex. -/
example {X : SSet.{u}} (V : Set (X _⦋0⦌)) {n : ℕ} (σ : Δ[n] ⟶ X)
    (hσ : ∀ i : Fin (n + 1),
      X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op
        (SSet.yonedaEquiv σ) ∈ V) :
    ∃ σ' : Δ[n] ⟶ (SSet.Subcomplex.full V : SSet.{u}),
      σ' ≫ (SSet.Subcomplex.full V).ι = σ :=
  SSet.Subcomplex.exists_factorThru_full_ι σ hσ

#print axioms idEdge_notMem_full_singleton
#print axioms preimage_full_singleton_constZeroMap
#print axioms full_singleton_ι_innerFibration
#print axioms SSet.Subcomplex.exists_factorThru_full_ι

end MathlibExtTest.AlgebraicTopology.SimplicialSet.FullSubcomplexTest

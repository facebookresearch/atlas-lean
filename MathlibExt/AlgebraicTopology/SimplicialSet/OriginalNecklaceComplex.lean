/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalTwoBeadSupport

/-!
# Native full necklace complexes

A necklace retains all original ordinal vertices. Its complete simplices
are precisely those that cross none of its supplied joints. The complex
uses the same native full two-bead faces, and original ordinal maps act
through literal standard-simplex maps.
-/

@[expose] public section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.OriginalNecklace

/-- The complete original necklace, cut at every supplied original joint. -/
def complex {n : ℕ} (J : Finset (Fin (n + 1))) : (Δ[n] : SSet.{u}).Subcomplex :=
  ⨅ j ∈ J, OriginalTwoBead.union j

/-- A complete original simplex crosses none of the original necklace joints. -/
theorem mem_complex_iff {n d : ℕ} (J : Finset (Fin (n + 1)))
    (s : (Δ[n] : SSet.{u}) _⦋d⦌) :
    s ∈ (complex J).obj (op ⦋d⦌) ↔
      ∀ j ∈ J, (∀ i, s i ≤ j) ∨ (∀ i, j ≤ s i) := by
  simp only [complex, Subfunctor.iInf_obj, Set.mem_iInter, OriginalTwoBead.mem_union_iff]

/-- The one-cut complex is the same original complete two-bead union. -/
theorem complex_singleton {n : ℕ} (j : Fin (n + 1)) :
    complex.{u} {j} = OriginalTwoBead.union j := by
  simp [complex]

/-- Adding original joints retains the full native intersection, with no simplex removed otherwise. -/
theorem complex_union {n : ℕ} (J K : Finset (Fin (n + 1))) :
    complex.{u} (J ∪ K) = complex J ⊓ complex K := by
  ext q s
  simp only [complex, Subfunctor.iInf_obj, Set.mem_iInter, Subfunctor.min_obj,
    Set.mem_inter_iff, Finset.mem_union, or_imp, forall_and]

/-- With just its original endpoints the necklace is the full original bead. -/
theorem complex_endpoints {n : ℕ} :
    complex.{u} ({0, Fin.last n} : Finset (Fin (n + 1))) = ⊤ := by
  apply top_unique
  rintro ⟨⟨d⟩⟩ s _
  apply (mem_complex_iff _ s).mpr
  intro j hj
  rcases Finset.mem_insert.mp hj with rfl | hj
  · exact Or.inr (fun i => Fin.zero_le (s i))
  · have h : j = Fin.last n := Finset.mem_singleton.mp hj
    subst j
    exact Or.inl (fun i => Fin.le_last (s i))

/-- Every original vertex is retained by the full necklace. -/
theorem vertex_mem {n : ℕ} (J : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    stdSimplex.obj₀Equiv.symm i ∈ (complex.{u} J).obj (op ⦋0⦌) := by
  apply (mem_complex_iff _ _).mpr
  intro j _
  rcases le_total i j with h | h
  · exact Or.inl (fun _ => h)
  · exact Or.inr (fun _ => h)

/-- The entire original vertex prism lies in the full original necklace. -/
theorem vertex_prism_mem {n d : ℕ} (J : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (a : (Δ[0] : SSet.{u}) _⦋d⦌) :
    (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i)).app (op ⦋d⦌) a ∈
      (complex.{u} J).obj (op ⦋d⦌) := by
  apply (mem_complex_iff _ _).mpr
  intro j _
  rcases le_total i j with h | h
  · exact Or.inl (fun _ => h)
  · exact Or.inr (fun _ => h)

/-- The actual original vertex map, retaining every degree of its native prism. -/
def vertexMap {n : ℕ} (J : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    (Δ[0] : SSet.{u}) ⟶ complex.{u} J :=
  Subcomplex.lift (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i)) (by
    intro q s hs
    obtain ⟨a, rfl⟩ := hs
    exact vertex_prism_mem J i a)

/-- The whole original vertex map reads back its literal standard-simplex map. -/
@[reassoc]
theorem vertexMap_ι {n : ℕ} (J : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    vertexMap.{u} J i ≫ (complex J).ι =
      SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i) := rfl

/-- An original ordinal map carries every complete bead when each target joint has a source joint. -/
theorem map_mem_of_joints {n m d : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌)
    (J : Finset (Fin (n + 1))) (K : Finset (Fin (m + 1)))
    (h : ∀ j ∈ K, ∃ i ∈ J, f.toOrderHom i = j)
    (s : (Δ[n] : SSet.{u}) _⦋d⦌) (hs : s ∈ (complex J).obj (op ⦋d⦌)) :
    (SSet.stdSimplex.map f).app (op ⦋d⦌) s ∈ (complex K).obj (op ⦋d⦌) := by
  apply (mem_complex_iff _ _).mpr
  intro j hj
  obtain ⟨i, hi, rfl⟩ := h j hj
  rcases (mem_complex_iff J s).mp hs i hi with hl | hr
  · exact Or.inl (fun a => f.toOrderHom.monotone (hl a))
  · exact Or.inr (fun a => f.toOrderHom.monotone (hr a))

/-- The literal original necklace map induced by the original ordinal operator. -/
def map {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌)
    (J : Finset (Fin (n + 1))) (K : Finset (Fin (m + 1)))
    (h : ∀ j ∈ K, ∃ i ∈ J, f.toOrderHom i = j) :
    (complex.{u} J : SSet.{u}) ⟶ complex.{u} K :=
  Subcomplex.lift ((complex J).ι ≫ SSet.stdSimplex.map f) (by
    intro q s hs
    obtain ⟨a, rfl⟩ := hs
    exact map_mem_of_joints f J K h a.val a.property)

/-- The whole original necklace map keeps its original standard-simplex inclusion equation. -/
@[reassoc]
theorem map_ι {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌)
    (J : Finset (Fin (n + 1))) (K : Finset (Fin (m + 1)))
    (h : ∀ j ∈ K, ∃ i ∈ J, f.toOrderHom i = j) :
    map.{u} f J K h ≫ (complex K).ι =
      (complex J).ι ≫ SSet.stdSimplex.map f := rfl

/-- The original necklace object data, including both original joints. -/
structure Data where
  /-- The entire original ordinal vertex set has this dimension. -/
  dimension : ℕ
  /-- The exact original joints. -/
  joints : Finset (Fin (dimension + 1))
  /-- The same original initial endpoint is a joint. -/
  source_joint : (0 : Fin (dimension + 1)) ∈ joints
  /-- The same original terminal endpoint is a joint. -/
  target_joint : Fin.last dimension ∈ joints

/-- The actual native simplicial set of the supplied original necklace. -/
abbrev Data.object (T : Data) : SSet.{u} := complex T.joints

/-- The actual native initial vertex map. -/
def Data.source (T : Data) : (Δ[0] : SSet.{u}) ⟶ T.object := vertexMap T.joints 0

/-- The actual native terminal vertex map. -/
def Data.target (T : Data) : (Δ[0] : SSet.{u}) ⟶ T.object :=
  vertexMap T.joints (Fin.last T.dimension)

end SSet.OriginalNecklace

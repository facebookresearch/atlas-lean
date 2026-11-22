/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CartesianCriticalMarkingPushouts
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCriticalRootMarking
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeAction

/-!
# Whole original path representatives of every new critical coefficient mark

The actual original final edge embeds the full interval cone at the
original predecessor. For a marked maximum change, its lower path is
the entire original source subset and its upper path is the entire
target subset with the final vertex erased. Acting on the actual
crossing interval cone edge recovers the supplied whole coefficient
edge, preserving every remaining original vertex and its inclusion.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- The actual original critical image edge supplies its whole lifted ordinal operator. -/
def coneCriticalEdgeOrder (n : ℕ) : Vertex.{u} 1 →o Vertex.{u} (n + 2) :=
  (stdSimplex.asOrderHom (cartesianCriticalImageEdge.{u} n)).uliftMap

/-- The original critical edge starts at precisely the original predecessor. -/
theorem coneCriticalEdgeOrder_bot (n : ℕ) :
    coneCriticalEdgeOrder.{u} n ⊥ = coneCriticalPrevious n := rfl

/-- The same original critical edge ends at the unchanged original final vertex. -/
theorem coneCriticalEdgeOrder_top (n : ℕ) :
    coneCriticalEdgeOrder.{u} n ⊤ = coneCriticalLast n := rfl

/-- Every original vertex of that exact critical interval has the same collapsed maximum. -/
theorem coneCriticalEdgeOrder_collapsed (n : ℕ) (i : Vertex.{u} 1) :
    coneCriticalMaximumCollapse n (coneCriticalEdgeOrder n i) = ULift.up (Fin.last (n + 1)) := by
  rcases i with ⟨i⟩
  fin_cases i
  · exact coneCriticalMaximumCollapse_previous n
  · exact coneCriticalMaximumCollapse_last n

/-- The original critical predecessor is strictly below the same original final vertex. -/
theorem coneCriticalPrevious_lt_last (n : ℕ) :
    coneCriticalPrevious.{u} n < coneCriticalLast n := by
  change n + 1 < n + 2
  omega

/-- Every original vertex other than the final one is bounded by the original predecessor. -/
theorem coneCritical_le_previous_of_ne_last (n : ℕ) (i : Vertex.{u} (n + 2))
    (hi : i ≠ coneCriticalLast n) : i ≤ coneCriticalPrevious n := by
  rcases i with ⟨i⟩
  cases i using Fin.lastCases with
  | last => exact (hi rfl).elim
  | cast i =>
    change i.val ≤ n + 1
    have h := i.isLt
    omega

/-- The entire original source subset is its actual path to the original critical predecessor. -/
def coneCriticalEdgeLowerPath (n : ℕ) (i : Vertex.{u} (n + 2))
    (e : (nerve (ConeSubset i)) _⦋1⦌) (h₀ : (e.obj 0).maximum = coneCriticalPrevious n) :
    SimplicialThickening.Path i (coneCriticalPrevious n) where
  I := (e.obj 0).vertices
  left := (e.obj 0).mem
  right := h₀ ▸ (e.obj 0).maximum_mem
  left_le := (e.obj 0).lower
  le_right k hk := h₀ ▸ (e.obj 0).le_maximum k hk

/-- The whole original upper path erases precisely the final vertex from the actual target subset. -/
def coneCriticalEdgeUpperPath (n : ℕ) (i : Vertex.{u} (n + 2))
    (e : (nerve (ConeSubset i)) _⦋1⦌) (h₀ : (e.obj 0).maximum = coneCriticalPrevious n) :
    SimplicialThickening.Path i (coneCriticalPrevious n) where
  I := (e.obj 1).vertices.erase (coneCriticalLast n)
  left := Finset.mem_erase.mpr ⟨by
    have hi : i ≤ coneCriticalPrevious n := h₀ ▸ (e.obj 0).le_maximum i (e.obj 0).mem
    exact ne_of_lt (hi.trans_lt (coneCriticalPrevious_lt_last.{u} n)), (e.obj 1).mem⟩
  right := Finset.mem_erase.mpr ⟨ne_of_lt (coneCriticalPrevious_lt_last.{u} n),
    leOfHom (e.map (homOfLE (show (0 : Fin 2) ≤ 1 from Fin.zero_le _)))
      (h₀ ▸ (e.obj 0).maximum_mem)⟩
  left_le k hk := (e.obj 1).lower k (Finset.mem_erase.mp hk).2
  le_right k hk := coneCritical_le_previous_of_ne_last n k (Finset.mem_erase.mp hk).1

/-- The actual whole original path pair retains the source-to-target subset inclusion. -/
theorem coneCriticalEdgePath_subset (n : ℕ) (i : Vertex.{u} (n + 2))
    (e : (nerve (ConeSubset i)) _⦋1⦌) (h₀ : (e.obj 0).maximum = coneCriticalPrevious n) :
    (coneCriticalEdgeLowerPath n i e h₀).I ⊆ (coneCriticalEdgeUpperPath n i e h₀).I := by
  intro k hk
  apply Finset.mem_erase.mpr
  refine ⟨?_, leOfHom (e.map (homOfLE (show (0 : Fin 2) ≤ 1 from Fin.zero_le _))) hk⟩
  have h : k ≤ coneCriticalPrevious n := h₀ ▸ (e.obj 0).le_maximum k hk
  exact ne_of_lt (h.trans_lt (coneCriticalPrevious_lt_last.{u} n))

/-- The supplied original coefficient edge gives its full nerve edge of whole paths. -/
def coneCriticalEdgePathWord (n : ℕ) (i : Vertex.{u} (n + 2))
    (e : (nerve (ConeSubset i)) _⦋1⦌) (h₀ : (e.obj 0).maximum = coneCriticalPrevious n) :
    (nerve (SimplicialThickening.Path i (coneCriticalPrevious n))) _⦋1⦌ where
  obj t := if t = 0 then coneCriticalEdgeLowerPath n i e h₀ else coneCriticalEdgeUpperPath n i e h₀
  map {s t} f := ⟨⟨⟨by
    have h := leOfHom f
    fin_cases s <;> fin_cases t
    · exact Set.Subset.rfl
    · exact coneCriticalEdgePath_subset n i e h₀
    · norm_num at h
    · exact Set.Subset.rfl⟩⟩⟩

/-- The original interval cone starts with precisely its original root singleton. -/
def coneCriticalIntervalLower : ConeSubset (⊥ : Vertex.{u} 1) where
  vertices := {⊥}
  mem := Finset.mem_singleton_self _
  lower _ hk := (Finset.mem_singleton.mp hk).symm ▸ le_refl _

/-- Its original crossing edge ends at the whole original two-vertex subset. -/
def coneCriticalIntervalUpper : ConeSubset (⊥ : Vertex.{u} 1) where
  vertices := {⊥, ⊤}
  mem := Finset.mem_insert_self _ _
  lower _ _ := bot_le

/-- The SAME original interval cone crossing edge, retaining its full two subset vertices. -/
def coneCriticalIntervalWord : (coneWeight (⊥ : Vertex.{u} 1)).toSSet _⦋1⦌ where
  obj t := if t = 0 then coneCriticalIntervalLower else coneCriticalIntervalUpper
  map {s t} f := homOfLE (by
    have h := leOfHom f
    fin_cases s <;> fin_cases t
    · exact le_refl _
    · change ({⊥} : Finset (Vertex.{u} 1)) ⊆ {⊥, ⊤}
      exact Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)
    · norm_num at h
    · exact le_refl _)

/-- The actual original critical operator sends the original lower interval subset to the predecessor singleton. -/
theorem coneCriticalIntervalLower_image (n : ℕ) :
    (coneCriticalIntervalLower.image (coneCriticalEdgeOrder.{u} n)).vertices = {coneCriticalPrevious n} := by
  change ({⊥} : Finset (Vertex.{u} 1)).image (coneCriticalEdgeOrder n) = {coneCriticalPrevious n}
  rw [Finset.image_singleton, coneCriticalEdgeOrder_bot]

/-- The same original operator retains exactly both original critical edge endpoints. -/
theorem coneCriticalIntervalUpper_image (n : ℕ) :
    (coneCriticalIntervalUpper.image (coneCriticalEdgeOrder.{u} n)).vertices =
      {coneCriticalPrevious n, coneCriticalLast n} := by
  change ({⊥, ⊤} : Finset (Vertex.{u} 1)).image (coneCriticalEdgeOrder n) = _
  rw [Finset.image_insert, Finset.image_singleton, coneCriticalEdgeOrder_bot, coneCriticalEdgeOrder_top]

/-- Acting by the full original path word on the SAME original critical interval edge recovers the entire supplied
coefficient edge. -/
theorem coneCriticalEdgePath_represents (n : ℕ) (i : Vertex.{u} (n + 2))
    (e : (nerve (ConeSubset i)) _⦋1⦌)
    (h₀ : (e.obj 0).maximum = coneCriticalPrevious n)
    (h₁ : (e.obj 1).maximum = coneCriticalLast n) :
    (coneAction i (coneCriticalPrevious n)).hom.app (op ⦋1⦌)
      (coneCriticalEdgePathWord n i e h₀,
        (coneImage (coneCriticalEdgeOrder n) (⊥ : Vertex.{u} 1)).hom.app (op ⦋1⦌)
          coneCriticalIntervalWord) = e := by
  refine CategoryTheory.Functor.ext (fun t => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  fin_cases t
  · apply ConeSubset.ext
    have hp : (coneCriticalEdgeLowerPath n i e h₀).I.toFinite.toFinset = (e.obj 0).vertices := by
      ext k
      exact (coneCriticalEdgeLowerPath n i e h₀).I.toFinite.mem_toFinset
    change (coneCriticalEdgeLowerPath n i e h₀).I.toFinite.toFinset ∪
      (coneCriticalIntervalLower.image (coneCriticalEdgeOrder n)).vertices = (e.obj 0).vertices
    rw [hp, coneCriticalIntervalLower_image]
    exact Finset.union_eq_left.mpr (Finset.singleton_subset_iff.mpr (h₀ ▸ (e.obj 0).maximum_mem))
  · apply ConeSubset.ext
    have hp : (coneCriticalEdgeUpperPath n i e h₀).I.toFinite.toFinset =
        (e.obj 1).vertices.erase (coneCriticalLast n) := by
      ext k
      exact (coneCriticalEdgeUpperPath n i e h₀).I.toFinite.mem_toFinset
    change (coneCriticalEdgeUpperPath n i e h₀).I.toFinite.toFinset ∪
      (coneCriticalIntervalUpper.image (coneCriticalEdgeOrder n)).vertices = (e.obj 1).vertices
    rw [hp, coneCriticalIntervalUpper_image]
    have hprev : coneCriticalPrevious n ∈ (e.obj 1).vertices :=
      leOfHom (e.map (homOfLE (show (0 : Fin 2) ≤ 1 from Fin.zero_le _)))
        (h₀ ▸ (e.obj 0).maximum_mem)
    have hlast : coneCriticalLast n ∈ (e.obj 1).vertices := h₁ ▸ (e.obj 1).maximum_mem
    ext k
    simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (⟨_, hk⟩ | rfl | rfl)
      · exact hk
      · exact hprev
      · exact hlast
    · intro hk
      by_cases h : k = coneCriticalLast n
      · exact Or.inr (Or.inr h)
      · exact Or.inl ⟨h, hk⟩

end SSet.Marked.CoherentWeight

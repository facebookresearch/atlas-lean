/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Adam Kiezun
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.VermaPearlForward
import Mathlib.Tactic.FinCases

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels

open Finset BayesianDirichlet

/-- The 25 labeled DAGs on `Fin 3` as parent maps (`u ∈ dags3 i v` is the edge `u → v`),
ordered by edge count, then by the parent bitmasks of nodes `0, 1, 2`. Generated outside
Lean by brute force over all 512 parent maps on `Fin 3` (25 are acyclic). -/
def dags3 : Fin 25 → Fin 3 → Finset (Fin 3) :=
  ![![∅, ∅, ∅],         -- 0: no edges
    ![∅, ∅, {0}],       -- 1: 0→2
    ![∅, ∅, {1}],       -- 2: 1→2
    ![∅, {0}, ∅],       -- 3: 0→1
    ![∅, {2}, ∅],       -- 4: 2→1
    ![{1}, ∅, ∅],       -- 5: 1→0
    ![{2}, ∅, ∅],       -- 6: 2→0
    ![∅, ∅, {0, 1}],    -- 7: 0→2, 1→2
    ![∅, {0}, {0}],     -- 8: 0→1, 0→2
    ![∅, {0}, {1}],     -- 9: 0→1, 1→2
    ![∅, {2}, {0}],     -- 10: 2→1, 0→2
    ![∅, {0, 2}, ∅],    -- 11: 0→1, 2→1
    ![{1}, ∅, {0}],     -- 12: 1→0, 0→2
    ![{1}, ∅, {1}],     -- 13: 1→0, 1→2
    ![{1}, {2}, ∅],     -- 14: 1→0, 2→1
    ![{2}, ∅, {1}],     -- 15: 2→0, 1→2
    ![{2}, {0}, ∅],     -- 16: 2→0, 0→1
    ![{2}, {2}, ∅],     -- 17: 2→0, 2→1
    ![{1, 2}, ∅, ∅],    -- 18: 1→0, 2→0
    ![∅, {0}, {0, 1}],  -- 19: 0→1, 0→2, 1→2
    ![∅, {0, 2}, {0}],  -- 20: 0→1, 2→1, 0→2
    ![{1}, ∅, {0, 1}],  -- 21: 1→0, 0→2, 1→2
    ![{2}, {0, 2}, ∅],  -- 22: 2→0, 0→1, 2→1
    ![{1, 2}, ∅, {1}],  -- 23: 1→0, 2→0, 1→2
    ![{1, 2}, {2}, ∅]]  -- 24: 1→0, 2→0, 2→1

/-- Markov-equivalence class of `dags3 i`, computed outside Lean from the full
d-separation table (`DSeparatedPa (dags3 i) X Y Z` for all `X Y Z : Set (Fin 3)`, under the
definitions in `VermaPearl.lean`); labels in order of first occurrence. 11 classes, sizes
1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 6:
class 0 = {0}: no edges.
class 1 = {1, 6}: skeleton 0-2.
class 2 = {2, 4}: skeleton 1-2.
class 3 = {3, 5}: skeleton 0-1.
class 4 = {7}: skeleton 0-2 1-2, v-structure 0→2←1.
class 5 = {8, 12, 16}: skeleton 0-1 0-2, no v-structure.
class 6 = {9, 13, 14}: skeleton 0-1 1-2, no v-structure.
class 7 = {10, 15, 17}: skeleton 0-2 1-2, no v-structure.
class 8 = {11}: skeleton 0-1 1-2, v-structure 0→1←2.
class 9 = {18}: skeleton 0-1 0-2, v-structure 1→0←2.
class 10 = {19, 20, 21, 22, 23, 24}: skeleton 0-1 0-2 1-2. -/
def mec3 : Fin 25 → Fin 11 :=
  ![0, 1, 2, 3, 2, 3, 1, 4, 5, 6, 7, 8, 5, 6, 6, 7, 5, 7, 9, 10, 10, 10, 10, 10, 10]

/-- Topological ranks of `dags3 i` (0 at sources, else one more than the largest parent
rank): `u ∈ dags3 i v → rank3 i u < rank3 i v`, the acyclicity witnesses. -/
def rank3 : Fin 25 → Fin 3 → ℕ :=
  ![![0, 0, 0], ![0, 0, 1], ![0, 0, 1], ![0, 1, 0], ![0, 1, 0],
    ![1, 0, 0], ![1, 0, 0], ![0, 0, 1], ![0, 1, 1], ![0, 1, 2],
    ![0, 2, 1], ![0, 1, 0], ![1, 0, 2], ![1, 0, 1], ![2, 1, 0],
    ![2, 0, 1], ![1, 2, 0], ![1, 1, 0], ![1, 0, 0], ![0, 1, 2],
    ![0, 2, 1], ![1, 0, 2], ![1, 2, 0], ![2, 0, 1], ![2, 1, 0]]

instance dags3DecidableAdjacent {V : Type*} [DecidableEq V] (Pa : V → Finset V) (u w : V) :
    Decidable (Adjacent Pa u w) :=
  inferInstanceAs (Decidable (u ∈ Pa w ∨ w ∈ Pa u))

instance dags3DecidableVStructure {V : Type*} [DecidableEq V] (Pa : V → Finset V) (u w z : V) :
    Decidable (IsVStructure Pa u w z) :=
  inferInstanceAs (Decidable (u ≠ z ∧ u ∈ Pa w ∧ z ∈ Pa w ∧ ¬Adjacent Pa u z))

instance dags3DecidableIff {p q : Prop} [dp : Decidable p] [dq : Decidable q] :
    Decidable (p ↔ q) :=
  match dp, dq with
  | isTrue hp, isTrue hq => isTrue ⟨fun _ => hq, fun _ => hp⟩
  | isFalse hp, isFalse hq => isTrue ⟨fun h => absurd h hp, fun h => absurd h hq⟩
  | isTrue hp, isFalse hq => isFalse (fun h => hq (h.mp hp))
  | isFalse hp, isTrue hq => isFalse (fun h => hp (h.mpr hq))

theorem dags3_rank_lt_of_mem :
    ∀ (i : Fin 25) (u v : Fin 3), u ∈ dags3 i v → rank3 i u < rank3 i v := by
  decide

theorem dags3_mem_cases : ∀ s : Finset (Fin 3),
    s = ∅ ∨ s = {0} ∨ s = {1} ∨ s = {2} ∨ s = {0, 1} ∨ s = {0, 2} ∨ s = {1, 2} ∨
      s = {0, 1, 2} := by
  decide

theorem dags3_cyc_contra {Pa : Fin 3 → Finset (Fin 3)} (h : IsAcyclic Pa)
    (hc : (∃ v, v ∈ Pa v) ∨ (∃ u v, u ≠ v ∧ u ∈ Pa v ∧ v ∈ Pa u) ∨
      (∃ u v w, u ≠ v ∧ v ≠ w ∧ u ≠ w ∧ u ∈ Pa v ∧ v ∈ Pa w ∧ w ∈ Pa u)) :
    False := by
  obtain ⟨v, hv⟩ | ⟨u, v, _, huv, hvu⟩ | ⟨u, v, w, _, _, _, huv, hvw, hwu⟩ := hc
  · exact h v (Relation.TransGen.single hv)
  · exact h u ((Relation.TransGen.single huv).trans (Relation.TransGen.single hvu))
  · exact h u (((Relation.TransGen.single huv).trans (Relation.TransGen.single hvw)).trans
      (Relation.TransGen.single hwu))

theorem dags3_skel_eq_of_class :
    ∀ (i j : Fin 25), mec3 i = mec3 j →
      (∀ u w, Adjacent (dags3 i) u w ↔ Adjacent (dags3 j) u w) := by
  decide

theorem dags3_vstr_eq_of_class :
    ∀ (i j : Fin 25), mec3 i = mec3 j →
      (∀ u w z, IsVStructure (dags3 i) u w z ↔ IsVStructure (dags3 j) u w z) := by
  decide

theorem dags3_class_of_skel_vstr :
    ∀ (i j : Fin 25), (∀ u w, Adjacent (dags3 i) u w ↔ Adjacent (dags3 j) u w) →
      (∀ u w z, IsVStructure (dags3 i) u w z ↔ IsVStructure (dags3 j) u w z) →
      mec3 i = mec3 j := by
  decide

/-- Test: every table entry is acyclic (witnesses: `rank3`). -/
theorem isAcyclic_dags3 (i : Fin 25) : IsAcyclic (dags3 i) := by
  intro v h
  have key : ∀ {a b : Fin 3}, Relation.TransGen (fun u w => u ∈ dags3 i w) a b →
      rank3 i a < rank3 i b := by
    intro a b h
    induction h with
    | single hmem => exact dags3_rank_lt_of_mem i _ _ hmem
    | tail _ hmem ih => exact lt_trans ih (dags3_rank_lt_of_mem i _ _ hmem)
  exact absurd (key h) (lt_irrefl _)

/-- Test: the 25 table entries are pairwise distinct. -/
theorem dags3_injective : Function.Injective dags3 := by
  decide

/-- Test: the table lists every acyclic parent map on `Fin 3`. -/
theorem exists_dags3_eq {Pa : Fin 3 → Finset (Fin 3)} (h : IsAcyclic Pa) : ∃ i, dags3 i = Pa := by
  have hPa : Pa = ![Pa 0, Pa 1, Pa 2] := by funext v; fin_cases v <;> rfl
  revert h
  rw [hPa]
  intro h
  obtain h0|h0|h0|h0|h0|h0|h0|h0 := dags3_mem_cases (Pa 0) <;>
    obtain h1|h1|h1|h1|h1|h1|h1|h1 := dags3_mem_cases (Pa 1) <;>
    obtain h2|h2|h2|h2|h2|h2|h2|h2 := dags3_mem_cases (Pa 2) <;>
    rw [h0, h1, h2] <;> rw [h0, h1, h2] at h <;>
    (first | exact False.elim (dags3_cyc_contra h (by decide)) | decide)

/-- Verma-Pearl Theorem 1, enumerated on all 3-node DAGs: same d-separations iff same class. -/
theorem dags3_dSeparatedPa_iff (i j : Fin 25) :
    (∀ X Y Z, DSeparatedPa (dags3 i) X Y Z ↔ DSeparatedPa (dags3 j) X Y Z) ↔ mec3 i = mec3 j := by
  constructor
  · intro hall
    obtain ⟨hskel, hvstr⟩ :=
      (markovEquivalent_iff_dSeparatedPa_iff (isAcyclic_dags3 i)
        (isAcyclic_dags3 j)).mpr hall
    exact dags3_class_of_skel_vstr i j hskel hvstr
  · intro hclass
    exact (markovEquivalent_iff_dSeparatedPa_iff (isAcyclic_dags3 i)
      (isAcyclic_dags3 j)).mp
      ⟨dags3_skel_eq_of_class i j hclass, dags3_vstr_eq_of_class i j hclass⟩

/-- Headline: on structures, same skeleton and v-structures iff same d-separations. -/
example {V : Type*} [DecidableEq V] [Finite V] {Pa Pa' : V → Finset V}
    (h : IsAcyclic Pa) (h' : IsAcyclic Pa') :
    ((∀ u w, Adjacent Pa u w ↔ Adjacent Pa' u w) ∧
        ∀ u w z, IsVStructure Pa u w z ↔ IsVStructure Pa' u w z) ↔
      ∀ X Y Z, DSeparatedPa Pa X Y Z ↔ DSeparatedPa Pa' X Y Z :=
  markovEquivalent_iff_dSeparatedPa_iff h h'

/-- Headline: adjacent vertices are inseparable (Lemma 1, one direction). -/
example {V : Type*} {Pa : V → Finset V} {u w : V} (h : Adjacent Pa u w) (Z : Set V) :
    ¬DSeparatedPa Pa {u} {w} Z :=
  not_dSeparatedPa_of_adjacent h Z

end Cslib.MachineLearning.GraphicalModels

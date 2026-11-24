/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Double-cut-and-join distance formula

For two genomes `A`, `B` on the same `N` genes (any mix of linear and
circular chromosomes; extremities are gene ends; a genome partitions all
extremities into singletons and pairs), the adjacency graph `AG(A,B)` has
cycles and paths. With `C` cycles and `I` odd paths,
`d_DCJ(A,B) = N - (C + I/2)`, and an optimal sorting sequence is found in
`O(N)` time (Algorithm 2). The `O(N)` running-time reading needs a RAM cost
model and is context here.

Overlap (definitional): `WantedExt/Complexity/NPComplete/DCJMedianWanted.lean`
defines genomes, adjacencies, and DCJ operations for the NP median problem;
the distance formula is not proved there.

Sources: A. Bergeron, J. Mixtacki and J. Stoye, "A unifying view of genome
rearrangements", WABI 2006, LNBI 4175, Springer, pp. 163-173, 2006,
doi:10.1007/11851561_16, Theorem 1; DCJ operation of S. Yancopoulos,
O. Attie and R. Friedberg, Bioinformatics 21(16):3340-3346, 2005.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.Ring.Parity

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.DCJDistanceWanted

open Classical

variable (N : ℕ)

/-- Gene extremities: each gene contributes a tail and a head. -/
abbrev Extremity (N : ℕ) := Fin N × Fin 2

/-- A genome partitions all extremities into singletons and pairs. -/
def IsGenome (G : Finset (Finset (Extremity N))) : Prop :=
  (∀ E ∈ G, E.card ≤ 2) ∧ (∀ E₁ ∈ G, ∀ E₂ ∈ G, E₁ ≠ E₂ → Disjoint E₁ E₂) ∧
    ∀ x, ∃ E ∈ G, x ∈ E

/-- Union adjacency edges of two genomes (pairs only; singletons isolated). -/
noncomputable def unionEdges (A B : Finset (Finset (Extremity N))) :
    Finset (Extremity N × Extremity N) :=
  Finset.univ.filter fun p =>
    (∃ E ∈ A, p.1 ∈ E ∧ p.2 ∈ E ∧ p.1 ≠ p.2) ∨
      ∃ E ∈ B, p.1 ∈ E ∧ p.2 ∈ E ∧ p.1 ≠ p.2

/-- Reachability along union edges. -/
inductive Reaches (N : ℕ) (E : Finset (Extremity N × Extremity N)) :
    Extremity N → Extremity N → Prop where
  | refl (v) : Reaches N E v v
  | step (u v w) : Reaches N E u v → (v, w) ∈ E → Reaches N E u w

/-- Connected components of the adjacency graph. -/
noncomputable def components (E : Finset (Extremity N × Extremity N)) :
    Finset (Finset (Extremity N)) :=
  Finset.univ.filter fun K =>
    K.Nonempty ∧ (∀ u ∈ K, ∀ v ∈ K, Reaches N E u v) ∧
      ∀ w ∉ K, ∀ u ∈ K, ¬ Reaches N E u w

/-- Degree within an edge set. -/
noncomputable def deg (E : Finset (Extremity N × Extremity N))
    (v : Extremity N) : ℕ :=
  Finset.card (Finset.univ.filter fun w => (v, w) ∈ E ∨ (w, v) ∈ E)

/-- A component is a cycle: every vertex has degree two. -/
def IsCycleComp (E : Finset (Extremity N × Extremity N))
    (K : Finset (Extremity N)) : Prop :=
  ∀ v ∈ K, deg N E v = 2

/-- Edge count of a component (undirected: ordered pairs halved). -/
noncomputable def compEdges (E : Finset (Extremity N × Extremity N))
    (K : Finset (Extremity N)) : ℕ :=
  Finset.card (Finset.univ.filter
    fun p : Extremity N × Extremity N => p.1 ∈ K ∧ p.2 ∈ K ∧ p ∈ E) / 2

/-- Cycle count and odd-path count of the adjacency graph. -/
noncomputable def cycleCount N (E : Finset (Extremity N × Extremity N)) : ℕ :=
  Finset.card ((components N E).filter (IsCycleComp N E))

/-- Odd paths: non-cycle components with an odd edge count. -/
noncomputable def oddPathCount
    (E : Finset (Extremity N × Extremity N)) : ℕ :=
  Finset.card ((components N E).filter
    fun K => ¬ IsCycleComp N E K ∧ Odd (compEdges N E K))

/-- A DCJ step replaces the adjacencies at two vertices by at most two
new ones (membership form, no decidability needed). -/
def IsDCJStep (G G' : Finset (Finset (Extremity N)))
    (u v : Finset (Extremity N)) : Prop :=
  u ∈ G ∧ v ∈ G ∧ u ≠ v ∧
    ∃ a b : Finset (Finset (Extremity N)), ∃ e₁ e₂ f₁ f₂,
      (∀ E, E ∈ G' ↔ (E ∈ G ∧ E ≠ u ∧ E ≠ v) ∨ E ∈ a ∨ E ∈ b) ∧
      (∀ E ∈ a, E = e₁ ∨ E = e₂) ∧ ∀ E ∈ b, E = f₁ ∨ E = f₂

/-- Sorting by DCJ steps: chains from `A` to `B`. -/
inductive SortsByDCJ (N : ℕ) : Finset (Finset (Extremity N)) →
    Finset (Finset (Extremity N)) → List (Finset (Finset (Extremity N))) → Prop where
  | nil (G) : SortsByDCJ N G G []
  | cons (G G' H : Finset (Finset (Extremity N))) (u v)
      (rest : List (Finset (Finset (Extremity N)))) :
      IsDCJStep N G G' u v → SortsByDCJ N G' H rest →
        SortsByDCJ N G H (G' :: rest)

/-- DCJ distance: minimum sorting length over the assumed sorting
sequence. Characterized by `hd_le` (lower bound) and `hd_att` (attainment)
in the theorem below. -/
noncomputable def dcjDist (A B : Finset (Finset (Extremity N)))
    (h : ∃ seq : List (Finset (Finset (Extremity N))),
      SortsByDCJ N A B seq) : ℕ :=
  Nat.find (p := fun k => ∃ seq : List (Finset (Finset (Extremity N))),
    SortsByDCJ N A B seq ∧ seq.length = k)
    (by obtain ⟨s, hs⟩ := h; exact ⟨s.length, s, hs, rfl⟩)

/-- **DCJ distance formula** (Bergeron-Mixtacki-Stoye 2006, Theorem 1):
hypotheses are two well-formed genomes on the same `N` genes (`hA`, `hB`),
the odd-path parity (`hodd`: `I` is even), and the distance
characterization (`hd_le`, `hd_att`). With `C` cycles and `I` odd paths in
the adjacency graph, the conclusion is `d_DCJ = N - (C + I / 2)` over `ℤ`.

Source: Bergeron-Mixtacki-Stoye (2006), Theorem 1. -/
theorem_wanted dcj_distance (A B : Finset (Finset (Extremity N)))
    (hA : IsGenome N A) (hB : IsGenome N B)
    (hex : ∃ seq : List (Finset (Finset (Extremity N))),
      SortsByDCJ N A B seq)
    (hd_le : ∀ seq : List (Finset (Finset (Extremity N))),
      SortsByDCJ N A B seq → dcjDist N A B hex ≤ seq.length)
    (hd_att : ∃ seq : List (Finset (Finset (Extremity N))),
      SortsByDCJ N A B seq ∧ dcjDist N A B hex = seq.length)
    (hodd : Even (oddPathCount N (unionEdges N A B))) :
    (dcjDist N A B hex : ℤ) = (N : ℤ) -
      ((cycleCount N (unionEdges N A B) +
        oddPathCount N (unionEdges N A B) / 2 : ℕ) : ℤ)

end WantedExt.Biology.ComputationalBiology.DCJDistanceWanted

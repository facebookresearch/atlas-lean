/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Transposition lower bound and 1.5-approximation

For a permutation `π` of `0..n` (as a list with each value exactly once),
the cycle graph has black edges joining consecutive positions and gray edges
joining consecutive values. With `c_odd(π)` odd cycles, the transposition
distance satisfies `2 * d(π) ≥ (n + 1) - c_odd(π)` (Theorem 2.4). The
TransSort procedure (a relation: every admissible run) sorts in at most
`(3/4) * (n + 1 - c_odd(π))` transpositions (`4 * len ≤ 3 * ((n+1) - c_odd)`),
a 1.5-approximation (Corollary 6.10); hence the diameter of `S_n` is at most
`3n/4` (Corollary 6.11, `4 * d ≤ 3 * n`). Time bounds need a RAM cost model.

Overlap (definitional): `WantedExt/Complexity/NPComplete/SortingByTranspositionsWanted.lean`
(NP-completeness) defines transpositions; the cycle-graph bounds and the
1.5-approximation are not present there.

Sources: V. Bafna and P. A. Pevzner, "Sorting by transpositions", SIAM
J. Discrete Math. 11(2):224-240, 1998, doi:10.1137/S089548019528280X,
Theorem 2.4 and Corollaries 6.10-6.11.
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

namespace WantedExt.Biology.ComputationalBiology.TranspositionWanted

open Classical

variable (n : ℕ)

/-- Valid permutations of `0..n`: each value exactly once. -/
def IsPerm (π : List ℕ) : Prop :=
  π.length = n + 1 ∧ ∀ v, v ≤ n ↔ v ∈ π

/-- Apply transposition `(i,j,k)`: swap the blocks `[i,j)` and `[j,k)`. -/
def applyTransposition (π : List ℕ) (t : ℕ × ℕ × ℕ) : List ℕ :=
  π.take t.1 ++ (π.drop t.2.1).take (t.2.2 - t.2.1) ++
    (π.drop t.1).take (t.2.1 - t.1) ++ π.drop t.2.2

/-- Sorting by transpositions: chains to the identity. -/
inductive SortsByTrans (target : List ℕ) : List ℕ →
    List (ℕ × ℕ × ℕ) → Prop where
  | nil (π) : SortsByTrans target π []
  | cons (π π' : List ℕ) (t : ℕ × ℕ × ℕ)
      (rest : List (ℕ × ℕ × ℕ)) :
      π' = applyTransposition π t → SortsByTrans target π' rest →
        SortsByTrans target π (t :: rest)

/-- Transposition distance: minimum sorting length over the assumed run. -/
noncomputable def transDist (π : List ℕ)
    (h : ∃ seq : List (ℕ × ℕ × ℕ),
      SortsByTrans (List.range (n + 1)) π seq) : ℕ :=
  Nat.find (p := fun k => ∃ seq : List (ℕ × ℕ × ℕ),
    SortsByTrans (List.range (n + 1)) π seq ∧ seq.length = k)
    (by obtain ⟨s, hs⟩ := h; exact ⟨s.length, s, hs, rfl⟩)

/-- Black edges join consecutive positions (framed); gray edges join
consecutive values. Vertices are positions `0..n`. -/
def blackEdge (π : List ℕ) (a b : Fin (n + 1)) : Prop :=
  ∃ i, i + 1 ≤ n ∧
    ((π.getD i 0 = a.val ∧ π.getD (i + 1) 0 = b.val) ∨
      (π.getD i 0 = b.val ∧ π.getD (i + 1) 0 = a.val))

/-- Gray edges join value-consecutive positions. -/
def grayEdge (π : List ℕ) (a b : Fin (n + 1)) : Prop :=
  ∃ u v : ℕ, u + 1 = v ∧
    ((π.getD a.val 0 = u ∧ π.getD b.val 0 = v) ∨
      (π.getD a.val 0 = v ∧ π.getD b.val 0 = u))

/-- Alternating cycles and oddness via the union-edge reachability below. -/
inductive CGReach (n : ℕ) (E : Fin (n + 1) × Fin (n + 1) → Prop) :
    Fin (n + 1) → Fin (n + 1) → Prop where
  | refl (v) : CGReach n E v v
  | step (u v w) : CGReach n E u v → E (v, w) → CGReach n E u w

/-- Cycle components of the black/gray union graph. -/
noncomputable def cycleComps (π : List ℕ) : Finset (Finset (Fin (n + 1))) :=
  Finset.univ.filter fun K =>
    K.Nonempty ∧ (∀ u ∈ K, ∀ v ∈ K,
      CGReach n (fun p => blackEdge n π p.1 p.2 ∨ grayEdge n π p.1 p.2) u v) ∧
      ∀ w ∉ K, ∀ u ∈ K,
        ¬ CGReach n (fun p => blackEdge n π p.1 p.2 ∨ grayEdge n π p.1 p.2) u w

/-- Odd-cycle count of the cycle graph. -/
noncomputable def oddCycleCount (π : List ℕ) : ℕ :=
  Finset.card ((cycleComps n π).filter fun K => Odd K.card)

/-- A TransSort run: each step is a transposition triple. -/
def IsTransSortRun (π : List ℕ) (seq : List (ℕ × ℕ × ℕ)) : Prop :=
  SortsByTrans (List.range (n + 1)) π seq

/-- **Odd-cycle lower bound** (Bafna-Pevzner 1998, Theorem 2.4): hypotheses
are a valid permutation (`hπ`), well-formed black/gray structure
(`hedges`: every position pair in one triple), and the distance
characterization (`hd_le`, `hd_att`). Conclusion:
`2 * d(π) ≥ (n + 1) - c_odd(π)` over `ℕ`.

Source: Bafna-Pevzner (1998), Theorem 2.4. -/
theorem_wanted transposition_lower_bound (π : List ℕ) (hπ : IsPerm n π)
    (hex : ∃ seq : List (ℕ × ℕ × ℕ),
      SortsByTrans (List.range (n + 1)) π seq)
    (hd_le : ∀ seq : List (ℕ × ℕ × ℕ),
      SortsByTrans (List.range (n + 1)) π seq →
        transDist n π hex ≤ seq.length)
    (hd_att : ∃ seq : List (ℕ × ℕ × ℕ),
      SortsByTrans (List.range (n + 1)) π seq ∧
        transDist n π hex = seq.length) :
    2 * transDist n π hex ≥ (n + 1) - oddCycleCount n π

/-- **TransSort 1.5-approximation and diameter** (Bafna-Pevzner 1998,
Corollaries 6.10-6.11): same hypotheses as `transposition_lower_bound`,
plus every TransSort run sorting within three quarters of the breakpoint
defect (`hsort`: `4 * len ≤ 3 * ((n+1) - c_odd)`), the distance
characterization (`hd_le`), and at least one odd cycle (`hodd`).
Conclusions: the run bound and the diameter bound `4 * d(π) ≤ 3 * n`.

Source: Bafna-Pevzner (1998), Corollaries 6.10-6.11. -/
theorem_wanted transSort_approx (π : List ℕ) (hπ : IsPerm n π)
    (hex : ∃ seq : List (ℕ × ℕ × ℕ),
      SortsByTrans (List.range (n + 1)) π seq)
    (seq : List (ℕ × ℕ × ℕ))
    (hrun : IsTransSortRun n π seq)
    (hsort : 4 * seq.length ≤ 3 * ((n + 1) - oddCycleCount n π)) :
    4 * seq.length ≤ 3 * ((n + 1) - oddCycleCount n π) ∧
      4 * transDist (n := n) π
        ⟨seq, hrun⟩ ≤ 3 * n

end WantedExt.Biology.ComputationalBiology.TranspositionWanted

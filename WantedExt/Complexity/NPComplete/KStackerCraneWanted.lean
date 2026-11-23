/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# K-STACKER CRANE PROBLEM is NP-complete

Source:
P. Crescenzi and V. Kann, *A compendium of NP optimization problems*, problem
MINIMUM K-STACKER CRANE PROBLEM;
G. N. Frederickson, M. S. Hecht, and C. E. Kim, "Approximation algorithms for some routing
problems", SIAM Journal on Computing 7 (1978), 178-193, doi:10.1137/0207017;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [ND26] STACKER-CRANE.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.StackerCraneWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KStackerCrane

open StackerCrane (StackerCraneInstance moves)

/-!
# K-STACKER CRANE PROBLEM is NP-complete

INSTANCE: a mixed graph `G = (V, A, E)` (`A` directed edges, `E` undirected edges), an initial
vertex `s ∈ V`, a length `l(e) ∈ ℕ` for each `e ∈ A ∪ E`, a positive integer `k`, and a positive
integer `K`.
QUESTION: is there a collection of `k` cycles, each containing the initial vertex `s`, that
collectively traverse each directed edge in `A` at least once, such that the maximum length of
the `k` cycles is at most `K`?

This is the decision version of MINIMUM K-STACKER CRANE PROBLEM from the Crescenzi-Kann
compendium, the `k`-person variant of STACKER-CRANE with a minimax objective treated
by Frederickson, Hecht and Kim. For `k = 1` it is STACKER-CRANE ([ND26], NP-complete by
Frederickson, Hecht and Kim) with the cycle required to pass through `s`; when `A` is nonempty
and `s` is the tail of a directed edge, every cycle that traverses all of `A` contains `s`.

The mixed graph, the lengths and the bound `K` are a STACKER-CRANE instance
(`WantedExt.Complexity.NPComplete.StackerCraneWanted`), reused with its `WellFormed` (simple
directed and undirected edge lists on `0, ..., n - 1`, `0 < K`) and its list of moves (each
directed edge from its tail to its head, each undirected edge in both directions); the instance
adds `s < n` and `0 < k` (`k` persons). A cycle is, as there, a closed walk given by a list of
indices of moves in which consecutive moves (cyclically) share an endpoint, so edges may repeat;
it contains `s` when its first move starts at `s` (every cycle through `s` can be rotated to
start there). The empty list is the trivial cycle at `s` (a person who stays at `s`). A
collection of `k` cycles is a list of `k` such lists, repetitions allowed. Numbers use the
binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: a STACKER-CRANE instance (vertex count `n`, directed edges `A` as
`(tail, head, length)`, undirected edges `E` as `(u, v, length)`, and the bound `K`), the
initial vertex `s`, and the number `k` of cycles. -/
abbrev KStackerCraneInstance := StackerCraneInstance × ℕ × ℕ

/-- Well-formedness of an instance: STACKER-CRANE's (simple edge lists, `0 < K`), `s < n`, and
`0 < k`. -/
def WellFormed (i : KStackerCraneInstance) : Prop :=
  StackerCrane.WellFormed i.1 ∧ i.2.1 < i.1.1 ∧ 0 < i.2.2

/-- `c` is a cycle containing `s`: consecutive moves (cyclically) share an endpoint, and the
first move, if any, starts at `s`. -/
def IsCycleAt (i : StackerCraneInstance) (s : ℕ) (c : List (Fin (moves i).length)) : Prop :=
  (∀ j (h : j < c.length),
      ((moves i)[c[j]]).2.1 = ((moves i)[c[(j + 1) % c.length]'(Nat.mod_lt _ (by omega))]).1) ∧
    ∀ h : 0 < c.length, ((moves i)[c[0]]).1 = s

/-- Some `k` cycles, each containing `s` and of length at most `K`, together traverse every
directed edge (index `< |A|` in `moves`). -/
def KStackerCraneFeasible (i : KStackerCraneInstance) : Prop :=
  ∃ cs : List (List (Fin (moves i.1).length)), cs.length = i.2.2 ∧
    (∀ c ∈ cs, IsCycleAt i.1 i.2.1 c ∧
      (c.map fun m => ((moves i.1)[m]).2.2).sum ≤ i.1.2.2.2) ∧
    ∀ a : Fin (moves i.1).length, (a : ℕ) < i.1.2.1.length → ∃ c ∈ cs, a ∈ c

open Classical in
/-- K-STACKER CRANE PROBLEM as a decision problem over bitstrings. -/
noncomputable def kStackerCraneDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := KStackerCraneInstance) x with
  | some i => decide (WellFormed i ∧ KStackerCraneFeasible i)
  | none => false

/-- **K-STACKER CRANE PROBLEM is NP-complete.** Source: Crescenzi and Kann, MINIMUM K-STACKER CRANE
PROBLEM; Frederickson, Hecht, and Kim (1978); Garey and Johnson (1979), [ND26]. -/
public theorem_wanted kStackerCrane_npComplete :
    kStackerCraneDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L kStackerCraneDec

end MetaMathlibExt.Complexity.NPComplete.KStackerCrane

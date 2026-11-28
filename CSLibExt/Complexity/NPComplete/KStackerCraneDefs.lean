/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# K-STACKER CRANE PROBLEM: definitions

Source:
P. Crescenzi and V. Kann, *A compendium of NP optimization problems*, problem
MINIMUM K-STACKER CRANE PROBLEM;
G. N. Frederickson, M. S. Hecht, and C. E. Kim, "Approximation algorithms for some routing
problems", SIAM Journal on Computing 7 (1978), 178-193, doi:10.1137/0207017;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [ND26] STACKER-CRANE.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.StackerCraneDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KStackerCrane

open StackerCrane (StackerCraneInstance moves)

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

/-- Some `k` cycles at `s` (possibly empty), each of length at most `K`, together traverse every
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

end MetaMathlibExt.Complexity.NPComplete.KStackerCrane

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Edit distance has no strongly subquadratic algorithm unless SETH fails

For sequences of length `n` over a 7-letter alphabet with unit edit costs,
write `EditFast` for solvability in time `O(n^{2-δ})` for some `δ > 0`
(a cost-model marker; the model itself is context). For Orthogonal Vectors
instances `A`, `B` of `N` binary vectors in dimension `d`, write `OVFast`
for solvability in `d^{O(1)} N^{2-δ}` time, and `SETH` for the Strong
Exponential Time Hypothesis. Theorem 5: `EditFast → OVFast` (the reduction);
since subquadratic OV refutes SETH (Williams 2005, `hwilliams`), CNF-SAT
would run in `M^{O(1)} 2^{(1-ε)N}` time.

Overlap: none (`CSLibExt/Algorithms/Lean/DynamicProgramming/EditDistance/Metric.lean`
explicitly lists Backurs-Indyk as not covered).

Sources: A. Backurs and P. Indyk, "Edit distance cannot be computed in
strongly subquadratic time (unless SETH is false)", SIAM J. Comput.
47(3):1087-1097, 2018, doi:10.1137/15M1053128, Theorem 5.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.SETHEditDistanceWanted

open Classical

/-- Unit costs over a 7-letter alphabet: matches free, else one. -/
def unitCost (a b : Option (Fin 7)) : ℝ :=
  match a, b with
  | none, none => 0
  | some x, some y => if x = y then 0 else 1
  | _, _ => 1

/-- A pairwise script alignment: equal-length rows. -/
structure ScriptAlignment where
  left : List (Option (Fin 7))
  right : List (Option (Fin 7))
  len_eq : left.length = right.length

/-- Sum of a real list. -/
def listSum : List ℝ → ℝ
  | [] => 0
  | v :: vs => v + listSum vs

/-- Script cost under unit costs. -/
def scriptCost (A : ScriptAlignment) : ℝ :=
  listSum ((A.left.zip A.right).map fun p => unitCost p.1 p.2)

/-- Validity: rows erase to the two strings. -/
def IsScriptOf (A : ScriptAlignment) (X Y : List (Fin 7)) : Prop :=
  A.left.filterMap id = X ∧ A.right.filterMap id = Y

/-- Unit-cost edit distance: infimum of script costs. -/
noncomputable def editDistance (X Y : List (Fin 7)) : ℝ :=
  sInf {v | ∃ A : ScriptAlignment, IsScriptOf A X Y ∧ scriptCost A = v}

/-- Orthogonal Vectors: two families of `N` binary vectors in dimension `d`
with an orthogonal pair (no coordinate both true). -/
def HasOrthogonalPair (d N : ℕ) (A B : Fin N → Fin d → Bool) : Prop :=
  ∃ i j, ∀ k, A i k = false ∨ B j k = false

/-- **Backurs-Indyk reduction** (2018, Theorem 5): hypotheses are the
`editDistance` characterization (`hδ_le`, `hδ_att`), length-`n` inputs
(`hlen`), an OV instance (`A`, `B`), and the fast-edit-distance marker
(`EditFast`: length-`n` edit distance over 7 letters in `O(n^{2-δ})`
time). Conclusion: the OV marker (`OVFast`: Orthogonal Vectors in
`d^{O(1)} N^{2-δ}` time).

Source: Backurs-Indyk (2018), Theorem 5. -/
theorem_wanted backurs_indyk (n : ℕ)
    (hδ_le : ∀ (X Y : List (Fin 7)) (A : ScriptAlignment),
      IsScriptOf A X Y → editDistance X Y ≤ scriptCost A)
    (hδ_att : ∀ X Y : List (Fin 7), ∃ A : ScriptAlignment,
      IsScriptOf A X Y ∧ editDistance X Y = scriptCost A)
    (hlen : 1 ≤ n)
    (d N : ℕ)
    (A B : Fin N → Fin d → Bool)
    (EditFast OVFast : Prop)
    (hfast : EditFast) :
    OVFast

/-- **SETH corollary** (Backurs-Indyk 2018): same hypotheses as
`backurs_indyk`, plus Williams' link (`hwilliams`: subquadratic OV refutes
the Strong Exponential Time Hypothesis `SETH`). Conclusion: fast edit
distance refutes SETH (so CNF-SAT on `N` variables and `M` clauses runs in
`M^{O(1)} 2^{(1-ε)N}` time).

Source: Backurs-Indyk (2018), via Williams (2005). -/
theorem_wanted seth_corollary (n : ℕ)
    (hδ_le : ∀ (X Y : List (Fin 7)) (A : ScriptAlignment),
      IsScriptOf A X Y → editDistance X Y ≤ scriptCost A)
    (hδ_att : ∀ X Y : List (Fin 7), ∃ A : ScriptAlignment,
      IsScriptOf A X Y ∧ editDistance X Y = scriptCost A)
    (hlen : 1 ≤ n)
    (d N : ℕ)
    (A B : Fin N → Fin d → Bool)
    (EditFast OVFast SETH : Prop)
    (hfast : EditFast)
    (hred : EditFast → OVFast)
    (hwilliams : OVFast → ¬ SETH) :
    ¬ SETH

end WantedExt.Biology.ComputationalBiology.SETHEditDistanceWanted

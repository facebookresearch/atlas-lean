/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Polynomial-time word problem for `Aut(Fₙ)` (Kourovka Notebook Problem 16.109)

Kourovka Notebook, Archive of Solved Problems, Problem 16.109 (V. E. Shpilrain): is there a
polynomial time algorithm for solving the word problem in `Aut(Fₙ)` (with respect to some particular
finite presentation), where `Fₙ` is the free group of rank `n ≥ 2`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FreeGroup.Basic
public import MathlibExt.Computability.BinaryNatEncoding

@[expose] public section

namespace MathlibExt.GroupTheory.AutFreeGroupWordProblemPolyTimeKourovka16Problem109Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.109 (V. E.
Shpilrain). UnsolvedMath record UM-00701300 (`KOU-16.109`), dataset ulamai/UnsolvedMath v1.8.0.

Polynomial time is the repository's bitstring complexity class `P`
(`MetaMathlibExt.ComplexityTheory`). A word over a finite generating family `gens : Fin k → Aut(Fₙ)`
is a list of letters `(i, b)`, `i : ℕ`, in the repository's bitstring encoding; the language accepts
the words whose letter indices are below `k` and which spell the identity. The target is stated for
every finite generating family: Schleimer notes (Remark 5.1) that a different generating set changes
running times by at most a multiplicative constant, so "some particular finite presentation" and
"every finite generating set" are equivalent.
-/

open MetaMathlibExt.ComplexityTheory MetaMathlibExt.BitstringEncoding

/-- The automorphism of `Fₙ` spelled by the word `w` over a generating family `gens` of `Aut(Fₙ)`:
the letter `(i, true)` is `gens i` and `(i, false)` is its inverse; a letter with `i ≥ k` is read as
the identity (the decision problem below rejects such words). -/
def evalAutWord {n k : ℕ} (gens : Fin k → MulAut (FreeGroup (Fin n))) (w : List (ℕ × Bool)) :
    MulAut (FreeGroup (Fin n)) :=
  FreeGroup.lift (fun i : ℕ => if h : i < k then gens ⟨i, h⟩ else 1) (FreeGroup.mk w)

open Classical in
/-- The word problem of `Aut(Fₙ)` for the generating family `gens`, as a decision problem on
bitstrings: an input that decodes (repository bitstring encoding of `List (ℕ × Bool)`) to a word
`w` is accepted iff every letter index of `w` is below `k` and `w` spells the identity
automorphism. Inputs that do not decode are rejected. -/
noncomputable def autWordProblem {n k : ℕ} (gens : Fin k → MulAut (FreeGroup (Fin n))) :
    DecisionProblem := fun x =>
  match bitDecode (α := List (ℕ × Bool)) x with
  | some w => decide ((∀ l ∈ w, l.1 < k) ∧ evalAutWord gens w = 1)
  | none => false

/-- Kourovka 16.109 (V. E. Shpilrain): for every `n ≥ 2` the word problem of `Aut(Fₙ)` is solvable
in polynomial time, stated for every finite generating family of `Aut(Fₙ)`. -/
def autFreeGroupWordProblemInP : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ (k : ℕ) (gens : Fin k → MulAut (FreeGroup (Fin n))),
    Subgroup.closure (Set.range gens) = ⊤ → autWordProblem gens ∈ P

/--
Resolved true: Schleimer (Theorem 5.2) proves that the word problem for `Aut(F_m)` is solvable in
polynomial time, and observes (Remark 5.1) that choosing a different generating set alters running
times by at most a multiplicative constant; the Kourovka Archive answers 16.109 "Yes, there is".
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.109 (V. E.
Shpilrain); resolution: S. Schleimer, Polynomial-time word problems, Comment. Math. Helv. 83 (2008),
741-765, Theorem 5.2 (the word problem for Aut(F_m) is polynomial time) and Remark 5.1 (choosing a
different generating set alters running times by at most a multiplicative constant); Kourovka
Archive, Problem 16.109 (Yes, there is), https://wrap.warwick.ac.uk/44057/.
-/
public theorem_wanted autFreeGroupWordProblemInP_holds : autFreeGroupWordProblemInP

end MathlibExt.GroupTheory.AutFreeGroupWordProblemPolyTimeKourovka16Problem109Wanted

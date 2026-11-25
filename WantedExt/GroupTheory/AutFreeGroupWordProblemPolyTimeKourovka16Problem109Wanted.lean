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

/-- **The automorphism spelled by a word.** Let $F_n$ be the free group on $n$ generators and let
$g_0, \dots, g_{k-1}$ be automorphisms of $F_n$. A word $w = ((i_1, b_1), \dots, (i_r, b_r))$ is a
finite list of letters $(i, b)$ with $i \in \mathbb{N}$ and $b$ a boolean. The automorphism
spelled by $w$ over $(g_i)$ is the product $a_1 a_2 \cdots a_r$ in $\operatorname{Aut}(F_n)$,
whose group operation is composition, where for $i_j < k$ the factor $a_j$ is $g_{i_j}$ if $b_j$ is
true and $g_{i_j}^{-1}$ if $b_j$ is false, and for $i_j \ge k$ the factor $a_j$ is the identity.
The empty word spells the identity. -/
def evalAutWord {n k : ℕ} (gens : Fin k → MulAut (FreeGroup (Fin n))) (w : List (ℕ × Bool)) :
    MulAut (FreeGroup (Fin n)) :=
  FreeGroup.lift (fun i : ℕ => if h : i < k then gens ⟨i, h⟩ else 1) (FreeGroup.mk w)

open Classical in
/-- **The word problem of Aut(Fₙ) for a family of automorphisms.** Let $F_n$ be the free group on
$n$ generators and let $g_0, \dots, g_{k-1}$ be automorphisms of $F_n$. A word is a finite list of
letters $(i, b)$ with $i \in \mathbb{N}$ and $b$ a boolean. The word problem for $(g_i)$ is the
decision problem that accepts a bitstring $x$ exactly when $x$ decodes, under the canonical
bitstring encoding of lists of pairs of a natural number and a boolean, to a word $w$ such that
every letter $(i, b)$ of $w$ has $i < k$ and the automorphism spelled by $w$ over $(g_i)$ is the
identity; here the letter $(i, \mathrm{true})$ stands for $g_i$ and $(i, \mathrm{false})$ for
$g_i^{-1}$. Bitstrings that do not decode to a word are rejected. -/
noncomputable def autWordProblem {n k : ℕ} (gens : Fin k → MulAut (FreeGroup (Fin n))) :
    DecisionProblem := fun x =>
  match bitDecode (α := List (ℕ × Bool)) x with
  | some w => decide ((∀ l ∈ w, l.1 < k) ∧ evalAutWord gens w = 1)
  | none => false

/-- **Polynomial-time word problem for Aut(Fₙ) (Kourovka 16.109).** The proposition that for
every $n \ge 2$, writing $F_n$ for the free group on $n$ generators, for every natural number $k$
and every family $g_0, \dots, g_{k-1}$ of automorphisms of $F_n$ that generates
$\operatorname{Aut}(F_n)$, the word problem of $\operatorname{Aut}(F_n)$ for the family
$(g_i)$, a decision problem on bitstrings, belongs to the complexity class P. -/
def autFreeGroupWordProblemInP : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ (k : ℕ) (gens : Fin k → MulAut (FreeGroup (Fin n))),
    Subgroup.closure (Set.range gens) = ⊤ → autWordProblem gens ∈ P

/--
**The word problem for Aut(Fₙ) is solvable in polynomial time.** Let $n \ge 2$ and let $F_n$ be the
free group on $n$ generators. For every natural number $k$ and every family
$g_0, \dots, g_{k-1}$ of automorphisms of $F_n$ that generates $\operatorname{Aut}(F_n)$, the word
problem of $\operatorname{Aut}(F_n)$ for this family belongs to the complexity class P. Here a word
is a finite list of letters $(i, b)$ with $i \in \mathbb{N}$ and $b$ a boolean, the letter
$(i, \mathrm{true})$ standing for $g_i$ and $(i, \mathrm{false})$ for $g_i^{-1}$, and the word
problem is the decision problem on bitstrings that accepts exactly the bitstrings that decode,
under the canonical bitstring encoding of lists of pairs of a natural number and a boolean, to a
word whose letter indices are all below $k$ and whose product in $\operatorname{Aut}(F_n)$ is the
identity; bitstrings that do not decode to a word are rejected.

Schleimer proves (Theorem 5.2) that the word problem for $\operatorname{Aut}(F_m)$ is solvable in
polynomial time, and observes (Remark 5.1) that changing the generating set alters running times
by at most a multiplicative constant; the Kourovka Archive answers 16.109 "Yes, there is".

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.109 (V. E.
Shpilrain); resolution: S. Schleimer, Polynomial-time word problems, Comment. Math. Helv. 83 (2008),
741-765, Theorem 5.2 (the word problem for Aut(F_m) is polynomial time) and Remark 5.1 (choosing a
different generating set alters running times by at most a multiplicative constant); Kourovka
Archive, Problem 16.109 (Yes, there is), https://wrap.warwick.ac.uk/44057/.
-/
public theorem_wanted autFreeGroupWordProblemInP_holds : autFreeGroupWordProblemInP

end MathlibExt.GroupTheory.AutFreeGroupWordProblemPolyTimeKourovka16Problem109Wanted

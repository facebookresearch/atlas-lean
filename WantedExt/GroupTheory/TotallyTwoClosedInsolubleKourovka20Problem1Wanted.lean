/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Insoluble totally 2-closed groups (Kourovka Notebook Problem 20.1)

Kourovka Notebook, Problem 20.1 (M. Arezoomand, M. A. Iranmanesh, C. E. Praeger, G. Tracey), marked
solved in the 21st issue: for `k ≥ 1`, a group `G` is totally `k`-closed if in each of its faithful
permutation representations, say on a set `Ω`, `G` is the largest subgroup of `Sym(Ω)` which leaves
invariant each of the `G`-orbits in the induced action on `Ωᵏ`. Are there any finite insoluble
totally `2`-closed groups with nontrivial Fitting subgroup?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Action.Faithful
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.Solvable

@[expose] public section

namespace MathlibExt.GroupTheory.TotallyTwoClosedInsolubleKourovka20Problem1Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 20.1 (M. Arezoomand, M. A. Iranmanesh, C.
E. Praeger, G. Tracey). UnsolvedMath record UM-00701660 (`KOU-20.1`), dataset ulamai/UnsolvedMath
v1.8.0.

A permutation leaves each orbit on `Ω²` invariant exactly when, for all `α, β`, some element of `G`
agrees with it at `α` and at `β`; `Ω` is an arbitrary type (for finite groups total `2`-closure on
finite sets implies it on arbitrary sets, as the resolving preprint notes). A nontrivial Fitting
subgroup is a nontrivial nilpotent normal subgroup.
-/

/-- The action of `G` on `Ω` is `2`-closed: every permutation `σ` of `Ω` that preserves each
`G`-orbit on ordered pairs (for all `α, β` some `g ∈ G` agrees with `σ` at `α` and at `β`) is
induced by an element of `G`. -/
def IsTwoClosedAction (G Ω : Type) [Group G] [MulAction G Ω] : Prop :=
  ∀ σ : Equiv.Perm Ω, (∀ α β : Ω, ∃ g : G, σ α = g • α ∧ σ β = g • β) →
    ∃ g : G, ∀ ω : Ω, σ ω = g • ω

/-- `G` is totally `2`-closed: in each faithful permutation representation of `G`, on any set
`Ω`, `G` is the largest subgroup of `Sym(Ω)` preserving each of its orbits on `Ω²`. -/
def IsTotallyTwoClosed (G : Type) [Group G] : Prop :=
  ∀ (Ω : Type) [MulAction G Ω], FaithfulSMul G Ω → IsTwoClosedAction G Ω

/-- Kourovka 20.1 (M. Arezoomand, M. A. Iranmanesh, C. E. Praeger, G. Tracey): there is a finite
insoluble totally `2`-closed group with nontrivial Fitting subgroup (equivalently, with a
nontrivial nilpotent normal subgroup). -/
def insolubleTotallyTwoClosedWithNontrivialFitting : Prop :=
  ∃ (G : Type) (_ : Group G), Finite G ∧ ¬ Group.IsSolvable G ∧ IsTotallyTwoClosed G ∧
    ∃ N : Subgroup G, N.Normal ∧ Group.IsNilpotent N ∧ N ≠ ⊥

/--
Resolved true: the Kourovka Notebook (21st issue) answers 20.1 "Yes, there are". Kinyon and Urban
(an AI-generated solution confirmed by G. Tracey) prove that `J₁ × C₁₃` is totally `2`-closed
(Section 3.34, Lemma 3.11), insoluble and has Fitting subgroup `C₁₃`; the Notebook also obtains `J₁
× C_p` for primes `p ∈ {13, 17}` or `p > 19` from Theorem 1.1 of
Arezoomand-Iranmanesh-Praeger-Tracey and Theorem 2 and Proposition 2 of Abdollahi-Arezoomand.
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 20.1 (M. Arezoomand, M. A. Iranmanesh, C.
E. Praeger, G. Tracey); resolution: M. Kinyon and J. Urban, Results on problems from the Kourovka
Notebook, preprint, version 4, 19 September 2026; M. Arezoomand, M. A. Iranmanesh, C. E. Praeger and
G. Tracey, Bull. Math. Sci. 14 (2024), no. 1, 2350004; A. Abdollahi and M. Arezoomand, J. Algebra
Appl. 17 (2018), no. 4, 1850065, Kinyon-Urban, Section 3.34 (Problem 20.1): J1 × C13 is totally
2-closed, insoluble, with Fitting subgroup C13 (Lemma 3.11: direct products of totally 2-closed
groups of coprime orders are totally 2-closed), an AI solution confirmed by G. Tracey; the Kourovka
Notebook (21st issue) also derives J1 × C_p (p ∈ {13, 17} or p > 19) from Theorem 1.1 of
Arezoomand-Iranmanesh-Praeger-Tracey and Theorem 2 and Proposition 2 of Abdollahi-Arezoomand,
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/kourovka-mathematics.pdf.
-/
public theorem_wanted insolubleTotallyTwoClosedWithNontrivialFitting_holds :
    insolubleTotallyTwoClosedWithNontrivialFitting

end MathlibExt.GroupTheory.TotallyTwoClosedInsolubleKourovka20Problem1Wanted

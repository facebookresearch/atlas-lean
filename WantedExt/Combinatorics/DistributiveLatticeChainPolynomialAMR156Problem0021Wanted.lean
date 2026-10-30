/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Real zeros of chain polynomials of distributive lattices (Stanley, Problem 20')

R. P. Stanley, Positivity Problems and Conjectures in Algebraic Combinatorics, Problem 20': for a
finite poset `P` let `c_k(P)` be the number of `k`-element chains (`c_0 = 1`) and `C(P, t) = ∑_k
c_k(P) t^k`. When `L` is a finite distributive lattice, is every zero of `C(L, t)` real?
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Algebra.Polynomial.RealRooted

@[expose] public section

namespace MathlibExt.Combinatorics.DistributiveLatticeChainPolynomialAMR156Problem0021Wanted

/-!
Source: R. P. Stanley, Positivity Problems and Conjectures in Algebraic Combinatorics (1999),
Problem 20' (chain polynomial of a finite distributive lattice). UnsolvedMath record UM-00801195
(`AMR-156-0021`), dataset ulamai/UnsolvedMath v1.8.0.

A finite distributive lattice is a type with `DistribLattice` and `Fintype` instances; chains are
finite subsets totally ordered by `≤` (the empty chain gives `c_0 = 1`). `C(L, t)` is nonzero, so
real-rootedness is `Polynomial.IsRealRooted` (MathlibExt) of its image in `ℂ[t]`. The (empty)
lattice on an empty type has `C = 1` and is harmless.
-/

open Classical in
/-- The chain polynomial `C(P, t) = ∑_k c_k(P) t^k` of a finite poset, where `c_k(P)` is the number
of `k`-element chains (`c_0 = 1`, the empty chain). -/
noncomputable def chainPolynomial (L : Type*) [PartialOrder L] [Fintype L] : Polynomial ℤ :=
  ∑ s ∈ (Finset.univ : Finset (Finset L)).filter (fun s : Finset L => IsChain (· ≤ ·) (s : Set L)),
    Polynomial.X ^ s.card

/-- Stanley's Problem 20' (Positivity Problems): for every finite distributive lattice `L`, every
zero of the chain polynomial `C(L, t)` is real. -/
def distributiveLatticeChainPolynomialRealRooted : Prop :=
  ∀ (L : Type) [DistribLattice L] [Fintype L],
    ((chainPolynomial L).map (Int.castRingHom ℂ)).IsRealRooted

/--
Resolved false: for naturally labeled `P`, real-rootedness of `C(J(P), t)` is equivalent to that of
`W(P, x)` (Stanley's text before Problem 20', after Brenti), and Stembridge's naturally labeled
`17`-element posets have `W`-polynomials with non-real zeros, so the distributive lattices `J(P)` of
their order ideals have chain polynomials with non-real zeros. Source: R. P. Stanley, Positivity
Problems and Conjectures in Algebraic Combinatorics (1999), Problem 20' (chain polynomial of a
finite distributive lattice); resolution: Stanley, Positivity Problems (1999), text before Problem
20', citing F. Brenti, Mem. Amer. Math. Soc. 413 (1989), Conj. 3; J. R. Stembridge, Counterexamples
to the poset conjectures of Neggers, Stanley, and Stembridge, Trans. Amer. Math. Soc. 359 (2007),
1115-1128; restated in C. A. Athanasiadis and K. Kalampogia-Evangelinou, Chain enumeration,
partition lattices and polynomials with only real roots, arXiv:2205.03796, Introduction, Stanley:
"When P is natural it can be shown [19, Conj. 3] that Problem 20 is equivalent to the following"
(Problem 20', with L = J(P)); Stembridge, Introduction: naturally labeled posets on 17 vertices with
non-real W-zeros; Athanasiadis–Kalampogia-Evangelinou: for finite distributive lattices the question
is equivalent to the naturally labeled poset conjecture of Neggers, "finally disproved by
Stembridge", https://arxiv.org/abs/2205.03796.
-/
public theorem_wanted distributiveLatticeChainPolynomialRealRooted_refuted :
    ¬ distributiveLatticeChainPolynomialRealRooted

end MathlibExt.Combinatorics.DistributiveLatticeChainPolynomialAMR156Problem0021Wanted

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Mark Sepanski
-/
module

public import Mathlib.Data.Finset.Grade
public import Mathlib.Data.Finsupp.Pointwise
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Grade

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Combinatorics 485, Combinatorics 486, Combinatorics 487, Combinatorics 488

/-!
# `MathlibExt.Combinatorics.Poset.Basic`

## References

* ec1 3.9.1 (for `moebiusAlgebraMul`)
* ec1 3.13 p 335 (for `flagFVector`, `flagHVector`)
* ec1 3.11 p 321 (for `IsHyperplaneArrangement`)
-/

namespace MetaMathlibExt

-- Combinatorics 485: Möbius Algebra Product

/-! ### Informal statement of `moebiusAlgebraMul`

Let L be a lattice, that is, a partially ordered set in which
any s,t∈ L have a least upper bound and a greatest lower
bound s∧ t, called their meet, and let R be a
commutative semiring with zero 0 and identity 1. The Möbius
algebra A(L,R) is the set of functions f: L→ R with
f(s)≠ 0 for only finitely many s∈ L. For f,g∈ A(L,R)
and c∈ R, the sum f+g and the scalar multiple cf are
given by (f+g)(s)=f(s)+g(s) and (cf)(s)=c f(s) for s∈ L,
and the zero element of A(L,R) is the function with value 0
at every s∈ L. Each s∈ L is identified with the function
in A(L,R) that has value 1 at s and value 0 at every
other element of L, so that f=∑_{s∈ L}f(s) s, a sum
with only finitely many nonzero terms. For f,g∈ A(L,R), the
Möbius algebra product f⋅ g∈ A(L,R) is the bilinear
extension of

  s⋅ t=s∧ t (s,t∈ L),

that is,

  (f⋅ g)(u)=∑_{s∧ t=u}f(s) g(t) (u∈ L),

the sum taken over all pairs (s,t)∈ L× L with
f(s)≠ 0, g(t)≠ 0 and s∧ t=u. If f or g is
the zero element, then so is f⋅ g. If L is empty, the
zero element is the only element of A(L,R).
-/

/-- **Möbius algebra product.** Let $L$ be a lattice with meet $\wedge$ and let $R$ be a
commutative semiring. The Möbius algebra $A(L, R)$ is the set of functions $f \colon L \to R$ with
$f(s) \neq 0$ for only finitely many $s \in L$. The product of $f, g \in A(L, R)$ is the function
$f \cdot g \in A(L, R)$ given by
$$(f \cdot g)(u) = \sum_{s \wedge t = u} f(s)\, g(t) \qquad (u \in L),$$
the sum taken over all pairs $(s, t) \in L \times L$ with $f(s) \neq 0$, $g(t) \neq 0$ and
$s \wedge t = u$. Equivalently, identifying each $s \in L$ with the function that is $1$ at $s$
and $0$ elsewhere, it is the bilinear extension of $s \cdot t = s \wedge t$.
-/
noncomputable def moebiusAlgebraMul {L R : Type*} [Lattice L]
    [CommSemiring R] (f g : L →₀ R) : L →₀ R :=
  f.sum fun s a => g.sum fun t b =>
    Finsupp.single (s ⊓ t) (a * b)

-- Combinatorics 486: Flag f-Vector


/-! ### Informal statement of `flagFVector`

Let P be a finite partially ordered set. For s,t∈ P, the
element t covers s if s<t and there is no u∈ P with
s<u<t, and t is minimal if there is no u∈ P with u<t.
Let ρ: P→ℤ_{≥ 0} be a function with
ρ(s)<ρ(t) whenever s<t, with ρ(t)=ρ(s)+1
whenever t covers s, and with ρ(t)=0 whenever t is
minimal. For a finite set S⊆ℤ_{≥ 0}, the
S-rank-selected subposet of P is

  P_S={t∈ P:ρ(t)∈ S}.

Elements x,y∈ P are comparable if x≤ y or y≤ x. A
chain in P_S is a subset C⊆ P_S any two elements of
which are comparable. It is maximal if no element of
P_S∖ C is comparable with every element of C, that
is, if C is not contained in a larger chain in P_S. The flag
f-vector of P is the function α_P on finite sets
S⊆ℤ_{≥ 0} given by

  α_P(S)=#{C:C is a maximal chain in P_S},

where # denotes the number of elements. If P_S=∅,
in particular if S=∅, the empty chain is the only
maximal chain in P_S, so α_P(S)=1. For
i∈ℤ_{≥ 0}, α_P({i}) is the number of
t∈ P with ρ(t)=i when there is at least one such t.
-/

/-- **Flag $f$-vector.** Let $P$ be a finite partially ordered set with a grade function
$\rho \colon P \to \mathbb{Z}_{\ge 0}$, that is, $\rho(s) < \rho(t)$ whenever $s < t$,
$\rho(t) = \rho(s) + 1$ whenever $t$ covers $s$ (that is, $s < t$ and no $u \in P$ satisfies
$s < u < t$), and $\rho(t) = 0$ whenever $t$ is minimal. For a finite set
$S \subseteq \mathbb{Z}_{\ge 0}$, let $P_S = \{t \in P : \rho(t) \in S\}$. The flag $f$-vector of
$P$ is the function $\alpha_P$ on finite sets $S \subseteq \mathbb{Z}_{\ge 0}$ such that
$\alpha_P(S)$ is the number of maximal chains in $P_S$, that is, of subsets $C \subseteq P_S$ any
two elements of which are comparable and such that every element of $P_S \setminus C$ is
incomparable with some element of $C$. In particular $\alpha_P(\emptyset) = 1$, the empty chain
being the only maximal chain in the empty poset.
-/
def flagFVector (P : Type*) [PartialOrder P] [Fintype P]
    [DecidableEq P] [DecidableLE P] [GradeMinOrder ℕ P]
    (S : Finset ℕ) : ℕ :=
  (Finset.univ.filter fun c : Finset P =>
    (∀ t ∈ c, grade ℕ t ∈ S) ∧
      (∀ x ∈ c, ∀ y ∈ c, x ≤ y ∨ y ≤ x) ∧
      ∀ t, grade ℕ t ∈ S → t ∉ c →
        ∃ x ∈ c, ¬(x ≤ t ∨ t ≤ x)).card

-- Combinatorics 487: Flag h-Vector


/-- **Flag $h$-vector.** Let $P$ be a finite partially ordered set with a grade function
$\rho \colon P \to \mathbb{Z}_{\ge 0}$, that is, $\rho(s) < \rho(t)$ whenever $s < t$,
$\rho(t) = \rho(s) + 1$ whenever $t$ covers $s$, and $\rho(t) = 0$ whenever $t$ is minimal. Let
$\alpha_P$ be the flag $f$-vector of $P$ with respect to $\rho$: for a finite set
$T \subseteq \mathbb{Z}_{\ge 0}$, $\alpha_P(T)$ is the number of maximal chains in the subposet
$\{t \in P : \rho(t) \in T\}$. The flag $h$-vector of $P$ is the integer-valued function $\beta_P$
on finite sets $S \subseteq \mathbb{Z}_{\ge 0}$ given by
$$\beta_P(S) = \sum_{T \subseteq S} (-1)^{|S \setminus T|} \alpha_P(T),$$
where the sum runs over all subsets $T$ of $S$ and $|S \setminus T|$ is the number of elements of
$S \setminus T$. In particular, $\beta_P(\emptyset) = \alpha_P(\emptyset) = 1$.
-/
def flagHVector (P : Type*) [PartialOrder P] [Fintype P]
    [DecidableEq P] [DecidableLE P] [GradeMinOrder ℕ P]
    (S : Finset ℕ) : ℤ :=
  ∑ T ∈ S.powerset, (-1) ^ (S \ T).card * (flagFVector P T : ℤ)

-- Combinatorics 488: Hyperplane Arrangement


/-- **Hyperplane arrangement.** Let $K$ be a field, let $V$ be a finite-dimensional vector space
over $K$, and let $E$ be an affine subspace of $V$, possibly empty. The dimension of a nonempty
affine subspace $v + W$, with $v \in V$ and $W$ a linear subspace of $V$, is $\dim W$. An affine
hyperplane of $E$ is a nonempty affine subspace $H$ of $V$ with $H \subseteq E$ and
$\dim H + 1 = \dim E$. A set $\mathcal{A}$ of affine subspaces of $V$ is a hyperplane arrangement
in $E$ if $\mathcal{A}$ is finite and every element of $\mathcal{A}$ is an affine hyperplane of $E$.

For $n \in \mathbb{Z}_{\ge 0}$, $V = K^n$ and $E = V$, the affine hyperplanes of $E$ are the sets
$\{v \in K^n : \alpha_1 v_1 + \cdots + \alpha_n v_n = a\}$
with $(\alpha_1, \ldots, \alpha_n) \in K^n$ nonzero and $a \in K$. The empty set is a hyperplane
arrangement in every $E$, and it is the only one when $E$ is empty or $\dim E = 0$.
-/
def IsHyperplaneArrangement {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (E : AffineSubspace K V) (A : Set (AffineSubspace K V)) :
    Prop :=
  A.Finite ∧ ∀ H ∈ A, H ≤ E ∧ (H : Set V).Nonempty ∧
    Module.finrank K H.direction + 1 =
      Module.finrank K E.direction

end MetaMathlibExt

end

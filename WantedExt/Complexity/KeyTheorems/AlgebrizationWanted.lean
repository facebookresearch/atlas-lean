/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Aaronson-Wigderson: the algebrization barrier

Source:
S. Aaronson and A. Wigderson, "Algebrization: A new barrier in complexity theory",
Proceedings of the Fortieth Annual ACM Symposium on Theory of Computing (STOC 2008),
731-740 (journal version in ACM Transactions on Computation Theory 1 (2009)).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Algebrization

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Aaronson-Wigderson: the algebrization barrier

A proof technique *algebrizes* if it also works relative to any *algebraic* oracle
pair: a base Boolean oracle `B` together with its algebraic extension `B̃`, where `B̃`
answers, for each input length `n`, queries (low-degree extension) for the multilinear
extension of the Boolean function `B` restricted to length `n`, over a finite
field `F_n` of characteristic 2 (the field schedule below: `F_n` is
`AdjoinRoot (irr n)`, the quotient of `Polynomial (ZMod 2)` by a monic irreducible
polynomial of degree `n + 1`, i.e. the field `GF(2 ^ (n + 1))`; the multilinear
extension below is stated over an arbitrary field). The multilinear extension is the unique
polynomial that is affine in each variable and agrees with the base function on
`{0, 1} ^ n`. The
counterexamples are *asymmetric*: they compare a class with access to the base oracle
against a class with access to the extension oracle, distinguishing the two oracles.
Aaronson and Wigderson showed there are algebraic oracle pairs on both sides of `P` vs
`NP`, with the asymmetry in opposite directions: one pair `A` with `P^A = NP^{Ã}`
(the base-oracle `P` already captures the extension-oracle `NP`), and one pair `B`
with `NP^B ⊄ P^{B̃}` (some language in the base-oracle `NP` is outside the
extension-oracle `P`: even the extension-oracle `P` cannot capture the
base-oracle `NP`). Mere inequality `P^{B̃} ≠ NP^B` would not suffice, since
it could hold because `P^{B̃}` contains a language outside `NP^B` while every
`NP^B` language remains in `P^{B̃}`, which would not obstruct an algebrizing
proof of `NP ⊆ P`. Hence no algebrizing proof technique can resolve `P` vs `NP` in either
direction: any such technique would have to prove the same statement relative to
every algebraic oracle pair. Giving `P` and `NP` the *same* extension oracle would
reduce the claim to ordinary same-oracle relativization and would not be the
Aaronson-Wigderson barrier. The extension oracle is encoded as a Boolean function
answering, for a query `(unary length, field element bits, j)`, bit `j` of the
representative of the multilinear extension at the field point. The length
parameter is given in unary (a bitstring of length `n`), so a polynomial-time
oracle machine has `Θ(n)` time to form queries, and the field schedule is
explicitly constructible at that scale. The field at length `n` is the
characteristic-2 field `GF(2 ^ (n + 1))`, presented as `AdjoinRoot (irr n)`
for a monic irreducible polynomial `irr n` of degree `n + 1` over `ZMod 2`;
it is a genuine finite field, not a composite residue ring (an earlier version
used `ZMod (2 ^ (n + 2) + 1)`, e.g. `ZMod 9` at `n = 1`). The encoding is the
power-basis encoding: a field element is the coefficient bitstring of its
representative polynomial of degree `< n + 1` in the basis `1, X, …, X ^ n`.
The irreducible polynomial is itself polynomial-time computable from the unary
length parameter (the `IsPolyTime` conjunct of `IsAlgebraicExtension`); this
is a true, non-vacuous requirement by Shoup's deterministic polynomial-time
algorithm for finding irreducible polynomials over finite fields (V. Shoup,
"New algorithms for finding irreducible polynomials over finite fields",
Mathematics of Computation 54 (1990), 435-447), and field operations on the
power-basis encoding are polynomial arithmetic mod `irr n`, polynomial-time
in `n`. The statement fixes this power-basis encoding relative to the chosen
`irr`; different choices of `irr` give isomorphic fields. (An earlier version
used the least prime above `2 ^ (n + 1)`; Bertrand's postulate only bounds
its bit length and does not give a deterministic polynomial-time algorithm
for finding it, so computability of that schedule was unsupported.)
-/

/-- **Multilinear extension of a Boolean function.** Identify the booleans true and false with $1$
and $0$. Let $F$ be a field, $n$ a natural number and $f : \{0,1\}^n \to \{0,1\}$.
The multilinear extension of $f$ at a point $x = (x_0, \dots, x_{n-1}) \in F^n$ is
$$\sum_{a \in \{0,1\}^n} f(a) \prod_{i=0}^{n-1} \ell_{a_i}(x_i),$$
where $f(a) \in \{0, 1\}$ is read in $F$, $\ell_1(t) = t$ and $\ell_0(t) = 1 - t$. -/
noncomputable def multilinearExt {n : ℕ} {F : Type*} [Field F]
    (f : (Fin n → Bool) → Bool) (x : Fin n → F) : F :=
  ∑ a : Fin n → Bool, (if f a then 1 else 0) *
    ∏ i : Fin n, (if a i then x i else 1 - x i)

/-- **Restriction of an oracle to inputs of length $n$.** For a function $B$ from bitstrings to
booleans and a natural number $n$, the restriction of $B$ to inputs of length $n$ is the function
on $\{0,1\}^n$ sending $a = (a_0, \dots, a_{n-1})$ to $B(a_0 a_1 \cdots a_{n-1})$, the value of
$B$ at the bitstring $a$. -/
def baseAt (B : List Bool → Bool) (n : ℕ) : (Fin n → Bool) → Bool :=
  fun a => B (List.ofFn a)

/-- **Coefficient bitstring of a polynomial over $\mathbb{F}_2$.** For a polynomial $q$ over
$\mathbb{F}_2 = \mathbb{Z}/2\mathbb{Z}$ and a natural number $n$, the coefficient bitstring of $q$
with parameter $n$ is the bitstring $b_0 b_1 \cdots b_{n+1}$ of length $n + 2$ in which $b_i$ is
true exactly when the coefficient of $X^i$ in $q$ equals $1$. -/
def polyBits (q : Polynomial (ZMod 2)) (n : ℕ) : List Bool :=
  (List.range (n + 2)).map (fun i => decide (q.coeff i = 1))

/-- **Answer bits of the algebraic extension oracle.** Let $n$ be a natural number, let $p$ be a
monic irreducible polynomial of degree $n + 1$ over $\mathbb{F}_2 = \mathbb{Z}/2\mathbb{Z}$, let
$F = \mathbb{F}_2[X]/(p)$ with $\alpha$ the class of $X$, let $B$ be a function from bitstrings to
booleans, and let $\tilde B_n$ be the multilinear extension over $F$ of the restriction of $B$ to
inputs of length $n$. Given a list $(e_0, e_1, \ldots)$ of bitstrings and an index $j$ with
$0 \le j \le n$, let $e_{i,k} \in \{0, 1\}$ be the bit of $e_i$ at position $k$, counting from
$0$, where a missing list entry or a missing bit counts as $0$, and let $x \in F^n$ be the point
with coordinates $x_i = \sum_{k=0}^{n} e_{i,k} \alpha^k$ for $i < n$. The answer bit is true
exactly when the coefficient of $\alpha^j$ in $\tilde B_n(x)$, written in the basis
$1, \alpha, \dots, \alpha^n$ of $F$ over $\mathbb{F}_2$, equals $1$.

The index $j$ ranges over $0, \dots, n$ only: an out-of-range index must be rejected by the
caller, not reduced modulo $n + 1$. -/
noncomputable def extAnswer {p : Polynomial (ZMod 2)} [Fact (Irreducible p)] (hp : p.Monic)
    (n : ℕ) (_hdeg : p.natDegree = n + 1) (B : List Bool → Bool)
    (pt : List (List Bool)) (j : Fin p.natDegree) : Bool :=
  decide (((AdjoinRoot.powerBasisAux' hp).repr
    (multilinearExt (baseAt B n)
      (fun i => AdjoinRoot.mk p (∑ k : Fin p.natDegree,
        Polynomial.monomial k.val
          (if (pt.getD i.val []).getD k.val false then (1 : ZMod 2) else 0))))
    j = 1))

/-- **Algebraic extension oracles.** Let $B$ and $O$ be oracles, that is, functions from
bitstrings to booleans. Then $O$ is an algebraic extension of $B$ when there are polynomials
$\pi_0, \pi_1, \pi_2, \ldots$ over $\mathbb{F}_2 = \mathbb{Z}/2\mathbb{Z}$, each $\pi_n$ monic and
irreducible of degree $n + 1$, with the following two properties, where $F_n$ is the field
$\mathbb{F}_2[X]/(\pi_n)$, $\alpha_n$ is the class of $X$ in $F_n$, and $\tilde B_n$ is the
multilinear extension over $F_n$ of the restriction of $B$ to inputs of length $n$. First, the
map sending a bitstring $u$ to the coefficient bitstring of $\pi_{|u|}$ with parameter $|u|$
(whose bits say which of the coefficients of $X^0, \dots, X^{|u|+1}$ equal $1$) is
polynomial-time computable. Second, let $y$ be a bitstring. If $y$ decodes, under the canonical
bitstring encoding of triples, to a triple $(u, (e_0, \dots, e_{m-1}), j)$ of a bitstring $u$, a
list of bitstrings and a natural number $j$ such that, writing $n = |u|$, we have $m = n$, every
$e_i$ has length $n + 1$ and $j \le n$, then $O(y)$ is true exactly when the coefficient of
$\alpha_n^j$ in $\tilde B_n(x)$, written in the basis $1, \alpha_n, \dots, \alpha_n^n$ of $F_n$
over $\mathbb{F}_2$, equals $1$. Here $x \in F_n^n$ is the point with coordinates
$x_i = \sum_{k=0}^{n} e_{i,k} \alpha_n^k$, where $e_{i,k} \in \{0, 1\}$ is the bit of $e_i$ at
position $k$, counting from $0$. Otherwise, in particular when $y$ does not decode, $O(y)$ is
false.

Every malformed query is answered false, so an oracle machine cannot route around the algebraic
structure through invalid encodings, and an out-of-range $j$ does not wrap around to
coordinate $0$. -/
def IsAlgebraicExtension (B O : List Bool → Bool) : Prop :=
  ∃ (irr : ℕ → Polynomial (ZMod 2))
    (hspec : ∀ n, (irr n).Monic ∧ (irr n).natDegree = n + 1 ∧ Irreducible (irr n)),
    IsPolyTime (fun u : List Bool => polyBits (irr u.length) u.length) ∧
    ∀ y : List Bool, O y =
      match MetaMathlibExt.BitstringEncoding.bitDecode
          (α := List Bool × List (List Bool) × ℕ) y with
      | some (u, pt, j) =>
        if h : pt.length = u.length ∧ (∀ e ∈ pt, e.length = u.length + 1) ∧
            j < u.length + 1 then
          @extAnswer (irr u.length) ⟨(hspec u.length).2.2⟩ (hspec u.length).1
            u.length (hspec u.length).2.1 B pt
            ⟨j, by rw [(hspec u.length).2.1]; exact h.2.2⟩
        else false
      | none => false

/-- **Aaronson-Wigderson: the algebrization barrier.** Call an oracle a function from bitstrings
to booleans. There are oracles $B$ and $\tilde B$ such that $\tilde B$ is an algebraic extension
of $B$ and $\mathsf{P}^B = \mathsf{NP}^{\tilde B}$. There are also oracles $B$ and $\tilde B$ such
that $\tilde B$ is an algebraic extension of $B$ and $\mathsf{NP}^B$ is not contained in
$\mathsf{P}^{\tilde B}$.

Source: S. Aaronson and A.
Wigderson, "Algebrization: A new barrier in complexity theory", Proceedings of the
Fortieth Annual ACM Symposium on Theory of Computing (STOC 2008), 731-740 (journal
version in ACM Transactions on Computation Theory 1 (2009)). -/
public theorem_wanted aaronson_wigderson_algebrization :
    (∃ B Bext : List Bool → Bool, IsAlgebraicExtension B Bext ∧
      PWithOracle B = NPWithOracle Bext) ∧
    (∃ B Bext : List Bool → Bool, IsAlgebraicExtension B Bext ∧
      ¬ (NPWithOracle B ⊆ PWithOracle Bext))

end MetaMathlibExt.Complexity.KeyTheorems.Algebrization

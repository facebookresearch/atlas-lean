/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Domination polynomial of the rook graph

Statements from Stephan Mertens, "Domination Polynomial of the
Rook Graph", *Journal of Integer Sequences* 27 (2024), Article
24.3.7
(<https://cs.uwaterloo.ca/journals/JIS/VOL27/Mertens/mertens6.html>).

A placement is a finset of cells in `Fin n × Fin m`.  Domination
uses MathlibExt's canonical `SimpleGraph.IsDominating` for
`SimpleGraph.rookGraph`; the provider theorem
`SimpleGraph.rookGraph_isDominating_iff` identifies this with the
coordinate condition that every cell shares its row or column
with a placed rook.  The paper's `E_{n,m}(k)` counts placements
meeting every row and every column.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.Combinatorics.SimpleGraph.RookGraph

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.GraphTheory.RookDominationPolynomialWanted

/-- **Rook placements covering all rows and columns.** For natural numbers $n$, $m$ and $k$,
$E_{n,m}(k)$ is the number of $k$-element sets of cells of the $n \times m$ board that contain a
cell in every row and a cell in every column (Mertens' $E_{n,m}(k)$). -/
def rookCoverCount (n m k : ℕ) : ℕ :=
  (((Finset.univ : Finset (Fin n × Fin m)).powersetCard k).filter
    (fun s => (∀ i : Fin n, ∃ j : Fin m, (i, j) ∈ s) ∧
      ∀ j : Fin m, ∃ i : Fin n, (i, j) ∈ s)).card

/-- **Dominating rook placements.** For natural numbers $n$, $m$ and $k$, $d_{n,m}(k)$ is the
number of $k$-element sets of cells of the $n \times m$ board that are dominating sets of the rook
graph on that board (Mertens' $d_{R_{n,m}}(k)$). -/
def rookDominatingCount (n m k : ℕ) : ℕ :=
  (((Finset.univ : Finset (Fin n × Fin m)).powersetCard k).filter
    (fun s : Finset (Fin n × Fin m) =>
      (SimpleGraph.rookGraph n m).IsDominating (s : Set (Fin n × Fin m)))).card

/-- **Domination polynomial of the rook graph.** For natural numbers $n$ and $m$, the rook
domination polynomial of the $n \times m$ board is the integer polynomial
$D_{n,m}(x) = \sum_{k=0}^{nm} d_{n,m}(k)\, x^k$, where $d_{n,m}(k)$ is the number of $k$-element
sets of cells of the $n \times m$ board that are dominating sets of the rook graph on that
board. -/
noncomputable def rookDominationPolynomial (n m : ℕ) : Polynomial ℤ :=
  ∑ k ∈ Finset.range (n * m + 1),
    Polynomial.C (rookDominatingCount n m k : ℤ) * Polynomial.X ^ k

/-- **Dominating rook placements via covering placements.** For natural numbers $n, m \ge 1$ and
$k$, let $d_{n,m}(k)$ be the number of $k$-element sets of cells of the $n \times m$ board that
are dominating sets of the rook graph on that board, and let $E_{a,b}(k)$ be the number of
$k$-element sets of cells of the $a \times b$ board that contain a cell in every row and a cell
in every column. Then
$$d_{n,m}(k) = \binom{nm}{k} -
\sum_{r=1}^{n} \sum_{c=1}^{m} \binom{n}{r} \binom{m}{c} E_{n-r,m-c}(k).$$

Source: Stephan Mertens, "Domination Polynomial of the Rook
Graph", Theorem 1 (`thm:R-E`). -/
theorem_wanted rookDominatingCount_eq_choose_sub_sum_rookCoverCount
    (n m k : ℕ) (hn : 0 < n) (hm : 0 < m) :
    (rookDominatingCount n m k : ℤ) =
      ((n * m).choose k : ℤ) -
        ∑ r ∈ Finset.Icc 1 n, ∑ c ∈ Finset.Icc 1 m,
          (n.choose r : ℤ) * (m.choose c : ℤ) *
            (rookCoverCount (n - r) (m - c) k : ℤ)

/-- **Recursion for rook placements covering all rows and columns.** For natural numbers
$n, m \ge 1$ and $k$, let $E_{a,b}(k)$ denote the number of $k$-element sets of cells of the
$a \times b$ board that contain a cell in every row and a cell in every column. Then
$$E_{n,m}(k) = \binom{nm}{k} -
\sum_{(r,c) \ne (0,0)} \binom{n}{r} \binom{m}{c} E_{n-r,m-c}(k),$$
where the sum runs over all pairs $(r, c) \ne (0, 0)$ with $0 \le r \le n$ and $0 \le c \le m$.

Source: Stephan Mertens, "Domination Polynomial of the Rook
Graph", Theorem 2 (`thm:E-recursion`). -/
theorem_wanted rookCoverCount_eq_choose_sub_sum_rookCoverCount
    (n m k : ℕ) (hn : 0 < n) (hm : 0 < m) :
    (rookCoverCount n m k : ℤ) =
      ((n * m).choose k : ℤ) -
        ∑ r ∈ Finset.range (n + 1), ∑ c ∈ Finset.range (m + 1),
          (n.choose r : ℤ) * (m.choose c : ℤ) *
            (rookCoverCount (n - r) (m - c) k : ℤ) *
            (if r = 0 ∧ c = 0 then 0 else 1)

/-- **Dominating rook placements at high density.** For natural numbers $n, m \ge 1$ and $k$ with
$k > nm - n - m - \min(n, m) + 2$, let $d_{n,m}(k)$ be the number of $k$-element sets of cells
of the $n \times m$ board that are dominating sets of the rook graph on that board. Then
$$d_{n,m}(k) = \binom{nm}{k} - nm \binom{(n-1)(m-1)}{k}.$$

Source: Stephan Mertens, "Domination Polynomial of the Rook
Graph", Corollary 3 (`cor:high-density`). -/
theorem_wanted rookDominatingCount_eq_choose_sub_mul_choose
    (n m k : ℕ) (hn : 0 < n) (hm : 0 < m)
    (hk : (n : ℤ) * m - n - m - (min n m : ℤ) + 2 < k) :
    (rookDominatingCount n m k : ℤ) =
      ((n * m).choose k : ℤ) -
        (n : ℤ) * m * (((n - 1) * (m - 1)).choose k : ℤ)

/-- **Single-sum formula for the rook domination polynomial.** For natural numbers $n, m \ge 1$,
the rook domination polynomial $D_{n,m}(x)$ of the $n \times m$ board, an integer polynomial,
satisfies
$$D_{n,m}(x) = ((1+x)^n - 1)^m -
(-1)^m \sum_{k=0}^{m-1} (-1)^k \binom{m}{k} ((1+x)^k - 1)^n.$$

Source: Stephan Mertens, "Domination Polynomial of the Rook
Graph", Theorem 4 (`thm:domination-polynomial`). -/
theorem_wanted rookDominationPolynomial_eq
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    rookDominationPolynomial n m =
      ((1 + Polynomial.X) ^ n - 1) ^ m -
        (-1 : Polynomial ℤ) ^ m *
          ∑ k ∈ Finset.range m,
            (-1 : Polynomial ℤ) ^ k * Polynomial.C (m.choose k : ℤ) *
              ((1 + Polynomial.X) ^ k - 1) ^ n

/-- **Symmetric formula for the rook domination polynomial.** For natural numbers $n, m \ge 1$,
the rook domination polynomial $D_{n,m}(x)$ of the $n \times m$ board, an integer polynomial,
satisfies
$$D_{n,m}(x) = ((1+x)^n - 1)^m + ((1+x)^m - 1)^n -
(-1)^{n+m} \sum_{\ell=0}^{n} \sum_{k=0}^{m} (-1)^{k+\ell}
\binom{n}{\ell} \binom{m}{k} (1+x)^{k\ell}.$$

Source: Stephan Mertens, "Domination Polynomial of the Rook
Graph", Corollary 5 (`cor:domination-polynomial`). -/
theorem_wanted rookDominationPolynomial_eq_symmetric
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    rookDominationPolynomial n m =
      ((1 + Polynomial.X) ^ n - 1) ^ m +
          ((1 + Polynomial.X) ^ m - 1) ^ n -
        (-1 : Polynomial ℤ) ^ (n + m) *
          ∑ ℓ ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (m + 1),
            Polynomial.C ((n.choose ℓ : ℤ) * (m.choose k : ℤ)) *
              (-1 : Polynomial ℤ) ^ (k + ℓ) *
              (1 + Polynomial.X) ^ (k * ℓ)

end MathlibExt.GraphTheory.RookDominationPolynomialWanted

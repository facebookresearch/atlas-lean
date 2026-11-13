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

/-- The number of `k`-rook placements on an `n × m` board meeting
every row and every column (Mertens' `E_{n,m}(k)`). -/
def rookCoverCount (n m k : ℕ) : ℕ :=
  (((Finset.univ : Finset (Fin n × Fin m)).powersetCard k).filter
    (fun s => (∀ i : Fin n, ∃ j : Fin m, (i, j) ∈ s) ∧
      ∀ j : Fin m, ∃ i : Fin n, (i, j) ∈ s)).card

/-- The number of dominating `k`-rook placements on an `n × m`
board (Mertens' `d_{R_{n,m}}(k)`), using the canonical
`SimpleGraph.IsDominating` predicate for `SimpleGraph.rookGraph`. -/
def rookDominatingCount (n m k : ℕ) : ℕ :=
  (((Finset.univ : Finset (Fin n × Fin m)).powersetCard k).filter
    (fun s : Finset (Fin n × Fin m) =>
      (SimpleGraph.rookGraph n m).IsDominating (s : Set (Fin n × Fin m)))).card

/-- The rook domination polynomial over `ℤ`, as the generating
polynomial of `rookDominatingCount`. -/
noncomputable def rookDominationPolynomial (n m : ℕ) : Polynomial ℤ :=
  ∑ k ∈ Finset.range (n * m + 1),
    Polynomial.C (rookDominatingCount n m k : ℤ) * Polynomial.X ^ k

/-- Mertens' Theorem 1, over `ℤ`: the dominating count is the
total placement count minus the placements whose nonempty rows
and columns form a smaller covered board.

Source: Stephan Mertens, "Domination Polynomial of the Rook
Graph", Theorem 1 (`thm:R-E`). -/
theorem_wanted rookDominatingCount_eq_choose_sub_sum_rookCoverCount
    (n m k : ℕ) (hn : 0 < n) (hm : 0 < m) :
    (rookDominatingCount n m k : ℤ) =
      ((n * m).choose k : ℤ) -
        ∑ r ∈ Finset.Icc 1 n, ∑ c ∈ Finset.Icc 1 m,
          (n.choose r : ℤ) * (m.choose c : ℤ) *
            (rookCoverCount (n - r) (m - c) k : ℤ)

/-- Mertens' Theorem 2, over `ℤ`: the recursion for the cover
count, with the `(0,0)` summand excluded.

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

/-- Mertens' Corollary 3, over `ℤ`: the high-density formula for
the dominating count.

Source: Stephan Mertens, "Domination Polynomial of the Rook
Graph", Corollary 3 (`cor:high-density`). -/
theorem_wanted rookDominatingCount_eq_choose_sub_mul_choose
    (n m k : ℕ) (hn : 0 < n) (hm : 0 < m)
    (hk : (n : ℤ) * m - n - m - (min n m : ℤ) + 2 < k) :
    (rookDominatingCount n m k : ℤ) =
      ((n * m).choose k : ℤ) -
        (n : ℤ) * m * (((n - 1) * (m - 1)).choose k : ℤ)

/-- Mertens' Theorem 4: the single-sum form of the rook domination
polynomial.

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

/-- Mertens' Corollary 5: the symmetric form of the rook
domination polynomial.

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

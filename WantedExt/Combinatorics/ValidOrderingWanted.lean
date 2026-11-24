/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Rearranging small sets for distinct partial sums

Statements from Noah Kravitz, "Rearranging Small Sets
for Distinct Partial Sums", *INTEGERS* 24 (2024), Article
A113 (<https://math.colgate.edu/~integers/vol24.html>).

An ordering `a₁, …, aₖ` of a finite set is *valid* if
its partial sums `a₁, a₁ + a₂, …, a₁ + ⋯ + aₖ` are
pairwise distinct. The empty partial sum `0` is not
counted: with it counted, `{6, 1, -7}` already has no
such ordering (exhaustive check), contradicting
Theorem 2; the form stated was verified by exhaustive
search on hundreds of small sets.

Theorem 1's bound `|A| ≤ log p / log log p` is read from
the journal PDF.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Combinatorics.Additive.FreimanHom
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.ZMod.Basic
public import MathlibExt.Combinatorics.DistinctPartialSumsOrdering

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.ValidOrderingWanted

/-- **Lev's rectification principle.** Let $\ell \ge 2$ be a natural number, $p$ a prime and
$A$ a subset of $\mathbb{Z}/p\mathbb{Z}$ with $|A| \le \lceil \log p / \log \ell \rceil$. Then
there are a finite set $B$ of integers and a map $f \colon \mathbb{Z}/p\mathbb{Z} \to \mathbb{Z}$
that is a Freiman isomorphism of order $\ell$ from $A$ to $B$: $f$ maps $A$ bijectively onto
$B$, and for all $a_1, \dots, a_\ell, b_1, \dots, b_\ell \in A$ we have
$f(a_1) + \cdots + f(a_\ell) = f(b_1) + \cdots + f(b_\ell)$ if and only if
$a_1 + \cdots + a_\ell = b_1 + \cdots + b_\ell$.

Source: Noah Kravitz, "Rearranging Small Sets for
Distinct Partial Sums", Theorem 3. -/
theorem_wanted exists_freimanIso_to_int (ℓ p : ℕ)
    (hℓ : 2 ≤ ℓ) (hp : p.Prime) (A : Finset (ZMod p))
    (hA : A.card ≤ ⌈Real.log p / Real.log ℓ⌉₊) :
    ∃ (B : Finset ℤ) (f : ZMod p → ℤ),
      IsAddFreimanIso ℓ (A : Set (ZMod p)) (B : Set ℤ) f

/-- **Theorem 1**: for a prime `p`, every `A ⊆ 𝔽_p \ {0}` with
`|A| ≤ log p / log log p` has a valid ordering (pairwise distinct
partial sums `a₁, a₁ + a₂, …`).

Source: Noah Kravitz, "Rearranging Small Sets for
Distinct Partial Sums", INTEGERS 24 (2024), Article A113,
Theorem 1. -/
theorem_wanted exists_distinct_partial_sums_ordering_zmod (p : ℕ) [Fact p.Prime]
    (A : Finset (ZMod p)) (h0 : 0 ∉ A)
    (hA : (A.card : ℝ) ≤ Real.log p / Real.log (Real.log p)) :
    ∃ l : List (ZMod p), List.Perm l A.toList ∧
      ((l.scanl (· + ·) 0).tail).Nodup

end MathlibExt.Combinatorics.ValidOrderingWanted

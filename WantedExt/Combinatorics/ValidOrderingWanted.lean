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

Not stated (see the source audit table): Theorem 1,
whose size bound is garbled in the extracted statement
by two-column interleaving.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Combinatorics.Additive.FreimanHom
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.ValidOrderingWanted

/-- **Valid orderings of finite sets of nonzero integers.** Every finite set $A$ of nonzero
integers has a valid ordering: its elements can be listed as $a_1, \dots, a_m$, each exactly
once, so that the partial sums $a_1, a_1 + a_2, \dots, a_1 + \cdots + a_m$ are pairwise
distinct. The empty sum $0$ is not counted among the partial sums.

Source: Noah Kravitz, "Rearranging Small Sets for
Distinct Partial Sums", Theorem 2. -/
theorem_wanted exists_distinct_partial_sums_ordering
    (A : Finset ℤ) (h0 : 0 ∉ A) :
    ∃ l : List ℤ, List.Perm l A.toList ∧
      ((l.scanl (· + ·) 0).tail).Nodup

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

end MathlibExt.Combinatorics.ValidOrderingWanted

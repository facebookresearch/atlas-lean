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

/-- **Theorem 2**: every finite subset of `ℤ \ {0}` has
a valid ordering, i.e., an ordering whose partial sums
are pairwise distinct.

Source: Noah Kravitz, "Rearranging Small Sets for
Distinct Partial Sums", Theorem 2. -/
theorem_wanted exists_distinct_partial_sums_ordering
    (A : Finset ℤ) (h0 : 0 ∉ A) :
    ∃ l : List ℤ, List.Perm l A.toList ∧
      ((l.scanl (· + ·) 0).tail).Nodup

/-- **Theorem 3** (Lev's rectification principle, as
quoted in the paper): for `ℓ ≥ 2`, if `A ⊆ 𝔽_p`
satisfies `|A| ≤ ⌈log p / log ℓ⌉`, then `A` is
`ℓ`-Freiman isomorphic to a set of integers. (For
`ℓ ≤ 1` the logarithmic bound is out of domain, hence
the hypothesis `2 ≤ ℓ`.)

Source: Noah Kravitz, "Rearranging Small Sets for
Distinct Partial Sums", Theorem 3. -/
theorem_wanted exists_freimanIso_to_int (ℓ p : ℕ)
    (hℓ : 2 ≤ ℓ) (hp : p.Prime) (A : Finset (ZMod p))
    (hA : A.card ≤ ⌈Real.log p / Real.log ℓ⌉₊) :
    ∃ (B : Finset ℤ) (f : ZMod p → ℤ),
      IsAddFreimanIso ℓ (A : Set (ZMod p)) (B : Set ℤ) f

end MathlibExt.Combinatorics.ValidOrderingWanted

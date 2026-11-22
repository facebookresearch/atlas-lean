/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Normal subgroups of exponent `p` in `p`-groups (Kourovka Notebook Problem 15.24)

Kourovka Notebook, Archive of Solved Problems, Problem 15.24 (Ya. G. Berkovich): if a finite
`p`-group has a subgroup of exponent `p` and order `pⁿ` and `p` is large relative to `n`, must it
have a normal subgroup of exponent `p` and order `pⁿ`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.PGroup

@[expose] public section

namespace MathlibExt.GroupTheory.NormalExponentPSubgroupKourovka15Problem24Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.24 (Ya. G.
Berkovich). UnsolvedMath record UM-00701112 (`KOU-15.24`), dataset ulamai/UnsolvedMath v1.8.0.

"Sufficiently large relative to `n`" is replaced by the explicit bound `p > n` of the resolution,
which implies the existential reading. Exponent `p` is written `x ^ p = 1` for all elements; for
order `pⁿ` with `n ≥ 1` this is exponent exactly `p`, and `n = 0` is the trivial case.
-/

/-- Kourovka 15.24 (Ya. G. Berkovich), with the bound `p > n` of its resolution: if a finite
`p`-group `G` has a subgroup of exponent `p` and order `pⁿ` and `p > n`, then `G` has a normal
subgroup of exponent `p` and order `pⁿ`. Exponent `p` is stated as `x ^ p = 1` for every element,
which for order `pⁿ` with `n ≥ 1` is exponent exactly `p`. -/
def normalExponentPSubgroupOfLargePrime : Prop :=
  ∀ p n : ℕ, p.Prime → n < p → ∀ (G : Type) [Group G] [Finite G], IsPGroup p G →
    (∃ H : Subgroup G, Nat.card H = p ^ n ∧ ∀ x ∈ H, x ^ p = 1) →
      ∃ N : Subgroup G, N.Normal ∧ Nat.card N = p ^ n ∧ ∀ x ∈ N, x ^ p = 1

/--
Resolved true: the Kourovka Archive answers "Yes, it is true if `p > n`" (A. Mann): by induction a
subgroup `H` of exponent `p` and order `pⁿ` may be taken normal in a maximal subgroup `M`; then `H ≤
ζ_{p-1}(M)`, and the elements of order `p` of `ζ_{p-1}(M)` form a normal subgroup of `G` containing
`H`. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.24 (Ya. G.
Berkovich); resolution: A. Mann, letter of 1 October 2002, as recorded in the Kourovka Archive,
Problem 15.24, Archive answer: Yes if p > n (H of exponent p and order p^n normal in a maximal
subgroup M lies in ζ_{p-1}(M), whose elements of order p form a normal subgroup of G),
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted normalExponentPSubgroupOfLargePrime_holds :
    normalExponentPSubgroupOfLargePrime

end MathlibExt.GroupTheory.NormalExponentPSubgroupKourovka15Problem24Wanted

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Exact Erdős-Ko-Rado bound for K(d)-families (Oberwolfach Reports 48/2006)

Oberwolfach workshop Combinatorics, Probability and Computing (2006), Conjecture 3 (D. Mubayi): for
`k ≥ d ≥ 3` and `n ≥ d k/(d - 1)`, every `K(d)`-family `G` of `k`-subsets of `[n]` has `|G| ≤ C(n -
1, k - 1)`, with equality only when all members of `G` share a point.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Nat.Choose.Basic

@[expose] public section

namespace MathlibExt.Combinatorics.ClusterFreeErdosKoRadoOWR1386Problem011Wanted

/-!
Source: D. Mubayi, in Combinatorics, Probability and Computing, Oberwolfach Reports 3 (2006), no.
48, p. 2922, Conjecture 3, DOI 10.4171/OWR/2006/48. UnsolvedMath record UM-30000604
(`OWR-1386-011`), dataset ulamai/UnsolvedMath v1.8.0.

A `K(d)`-family (source's definition): any `d` distinct members with union of size at most `2k` have
a common element. `[n]` is `Fin n`; `d` distinct members are an injective map from `Fin d`.
-/

/-- A `K(d)`-family of `k`-subsets of `Fin n`: every member has `k` elements, and any `d` distinct
members whose union has at most `2 k` elements have a common element. -/
def IsKdFamily (n k d : ℕ) (G : Finset (Finset (Fin n))) : Prop :=
  (∀ A ∈ G, A.card = k) ∧
    ∀ A : Fin d → Finset (Fin n), Function.Injective A → (∀ i, A i ∈ G) →
      (Finset.univ.biUnion A).card ≤ 2 * k → ∃ x, ∀ i, x ∈ A i

/-- Mubayi's conjecture (Oberwolfach Report 48/2006, Conjecture 3): for `3 ≤ d ≤ k` and
`n ≥ d k / (d - 1)`, every `K(d)`-family `G` of `k`-subsets of an `n`-set has
`|G| ≤ C(n - 1, k - 1)`, and equality holds only if all members of `G` share a point. -/
def kdFamilyErdosKoRado : Prop :=
  ∀ n k d : ℕ, 3 ≤ d → d ≤ k → (d : ℝ) * k / (d - 1) ≤ n →
    ∀ G : Finset (Finset (Fin n)), IsKdFamily n k d G →
      G.card ≤ (n - 1).choose (k - 1) ∧
        (G.card = (n - 1).choose (k - 1) → ∃ x, ∀ A ∈ G, x ∈ A)

/--
Resolved true: Currier proved that for `2 ≤ d ≤ k` and `n ≥ d k/(d - 1)` a family of `k`-subsets of
`[n]` with no `d` members having empty intersection and union of size at most `2k` has at most `C(n
- 1, k - 1)` members, with equality only for a full star when `d ≥ 3`, resolving Mubayi's
conjecture. Source: D. Mubayi, in Combinatorics, Probability and Computing, Oberwolfach Reports 3
(2006), no. 48, p. 2922, Conjecture 3, DOI 10.4171/OWR/2006/48; resolution: G. Currier, On the
d-cluster generalization of Erdős-Ko-Rado, J. Combin. Theory Ser. A 182 (2021), 105464,
arXiv:1812.11153, abstract and Theorem 2: for 2 ≤ d ≤ k and n ≥ dk/(d - 1), a family of k-subsets of
[n] with no d-cluster (d members with empty intersection and union of size at most 2k) has at most
C(n - 1, k - 1) members, with equality only for a full star (d ≥ 3); this resolves Mubayi's
conjecture, https://arxiv.org/abs/1812.11153.
-/
public theorem_wanted kdFamilyErdosKoRado_holds : kdFamilyErdosKoRado

end MathlibExt.Combinatorics.ClusterFreeErdosKoRadoOWR1386Problem011Wanted

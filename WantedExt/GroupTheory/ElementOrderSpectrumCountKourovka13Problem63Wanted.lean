/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Number of finite groups with a given spectrum (Kourovka Notebook Problem 13.63)

Kourovka Notebook, Archive of Solved Problems, Problem 13.63 (W. J. Shi): for `Γ ⊆ ℕ` let `h(Γ)` be
the number of non-isomorphic finite groups `G` with `π_e(G) = Γ`. Is there `k` such that for every
`Γ` either `h(Γ) ≤ k` or `h(Γ) = ∞`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

namespace MathlibExt.GroupTheory.ElementOrderSpectrumCountKourovka13Problem63Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 13.63 (W. J.
Shi). UnsolvedMath record UM-00700981 (`KOU-13.63`), dataset ulamai/UnsolvedMath v1.8.0.

`π_e(G)` is the set of element orders. `h(Γ) ≤ k` is stated as "among any `k + 1` finite groups with
spectrum `Γ` two are isomorphic" and `h(Γ) = ∞` as "for every `n` there are `n` pairwise
non-isomorphic finite groups with spectrum `Γ`", which avoids counting isomorphism classes directly.
-/

/-- The spectrum `π_e(G)`: the set of orders of elements of `G`. -/
def elementOrders (G : Type*) [Group G] : Set ℕ :=
  Set.range (orderOf : G → ℕ)

/-- `h(Γ) ≤ k`: among any `k + 1` finite groups with spectrum `Γ`, two are isomorphic. -/
def AtMostIsoClasses (Γ : Set ℕ) (k : ℕ) : Prop :=
  ∀ (G : Fin (k + 1) → Type) [∀ i, Group (G i)] [∀ i, Finite (G i)],
    (∀ i, elementOrders (G i) = Γ) → ∃ i j, i ≠ j ∧ Nonempty (G i ≃* G j)

/-- `h(Γ) = ∞`: for every `n` there are `n` pairwise non-isomorphic finite groups with
spectrum `Γ`. -/
def InfinitelyManyIsoClasses (Γ : Set ℕ) : Prop :=
  ∀ n : ℕ, ∃ (G : Fin n → Type) (_ : ∀ i, Group (G i)) (_ : ∀ i, Finite (G i)),
    (∀ i, elementOrders (G i) = Γ) ∧ ∀ i j, i ≠ j → IsEmpty (G i ≃* G j)

/-- Kourovka 13.63 (W. J. Shi): there is `k` such that for every `Γ ⊆ ℕ` the number `h(Γ)` of
isomorphism classes of finite groups `G` with `π_e(G) = Γ` is either at most `k` or infinite. -/
def spectrumGroupCountBoundedOrInfinite : Prop :=
  ∃ k : ℕ, ∀ Γ : Set ℕ, AtMostIsoClasses Γ k ∨ InfinitelyManyIsoClasses Γ

/--
Resolved false: the Kourovka Archive answers 13.63 "No, there is no such number": Zavarnitsine
proves `h(π_e(L₃(7^(3^r)))) = r + 1` for every `r ≥ 0`, so `h` takes every positive finite value and
no `k` works. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 13.63
(W. J. Shi); resolution: A. V. Zavarnitsine, J. Group Theory 7 (2004), no. 1, 81-97,
h(π_e(L_3(7^(3^r)))) = r + 1 for every r ≥ 0; Kourovka Archive, Problem 13.63 (answer: No, there is
no such number).
-/
public theorem_wanted spectrumGroupCountBoundedOrInfinite_refuted :
    ¬ spectrumGroupCountBoundedOrInfinite

end MathlibExt.GroupTheory.ElementOrderSpectrumCountKourovka13Problem63Wanted

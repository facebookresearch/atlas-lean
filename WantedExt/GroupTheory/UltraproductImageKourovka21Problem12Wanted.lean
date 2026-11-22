/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Homomorphic images of countable ultraproducts of groups (Kourovka Notebook Problem 21.12)

Kourovka Notebook, Problem 21.12 (G. M. Bergman), marked solved in the 21st issue: suppose that `𝒰`
is a nonprincipal ultrafilter on `ω`, and `B` is a group such that every element `b ∈ B` belongs to
a subgroup of `B` that is a homomorphic image of `ℤ^ω / 𝒰`. Must `B` then be a homomorphic image of
an ultraproduct group `(∏_{i ∈ ω} Gᵢ) / 𝒰` for some groups `Gᵢ`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Ultrafilter.Defs

@[expose] public section

namespace MathlibExt.GroupTheory.UltraproductImageKourovka21Problem12Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 21.12 (G. M. Bergman). UnsolvedMath record
UM-00002521 (`KOU-21.12`), dataset ulamai/UnsolvedMath v1.8.0.

Nonprincipal is `U ≤ cofinite`. A homomorphic image of an ultraproduct `(∏ Gᵢ) / U` is written as a
surjective homomorphism from `∏ Gᵢ` killing the families that are `1` at `U`-almost every index
(these form the kernel of `∏ Gᵢ → (∏ Gᵢ) / U`), and likewise for `ℤ^ω / U`. The question is posed
for a fixed `U`; since the answer is negative for every `U`, the target is stated for some `U`, so
that its refutation covers all `U`.
-/

/-- Every element of `B` lies in a subgroup of `B` that is a homomorphic image of the ultrapower
`ℤ^ω / U`, i.e. of `ℤ^ω` by a homomorphism killing the sequences that vanish `U`-almost
everywhere. -/
def IsLocallyUltrapowerImage (U : Ultrafilter ℕ) (B : Type) [Group B] : Prop :=
  ∀ b : B, ∃ (H : Subgroup B) (ψ : Multiplicative (ℕ → ℤ) →* H), b ∈ H ∧ Function.Surjective ψ ∧
    ∀ f : ℕ → ℤ, (∀ᶠ i in (U : Filter ℕ), f i = 0) → ψ (Multiplicative.ofAdd f) = 1

/-- Kourovka 21.12 (G. M. Bergman), for some nonprincipal ultrafilter `U` on `ℕ`: every group
`B` each of whose elements lies in a subgroup that is a homomorphic image of `ℤ^ω / U` is a
homomorphic image of an ultraproduct `(∏ᵢ Gᵢ) / U`, i.e. of `∏ᵢ Gᵢ` by a surjective homomorphism
killing every family that is `1` at `U`-almost every index. -/
def locallyUltrapowerImageIsUltraproductImage : Prop :=
  ∃ U : Ultrafilter ℕ, (U : Filter ℕ) ≤ Filter.cofinite ∧
    ∀ (B : Type) [Group B], IsLocallyUltrapowerImage U B →
      ∃ (G : ℕ → Type) (_ : ∀ i, Group (G i)) (φ : (∀ i, G i) →* B), Function.Surjective φ ∧
        ∀ f : ∀ i, G i, (∀ᶠ i in (U : Filter ℕ), f i = 1) → φ f = 1

/--
Resolved false: Corson (J. Algebra 681 (2025), Section 2) shows that for every nonprincipal
ultrafilter `U` on `ω` the abelian group `⊕ₙ Cₙ` with `Cₙ` finite cyclic of unbounded orders has
every element in a homomorphic image of `(∏ ℤ) / U`, but is not a homomorphic image of any
nonprincipal countable ultraproduct; the 21st issue of the Kourovka Notebook marks 21.12 solved
("No, it need not"). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 21.12 (G. M. Bergman);
resolution: S. M. Corson, On homomorphic images of ultraproducts, J. Algebra 681 (2025), 306-317,
arXiv:2503.09228, Section 2, proof of the negative answer to Question 3 (Bergman's Question 19): for
every nonprincipal ultrafilter U on ω the group ⊕ₙ Cₙ, Cₙ finite cyclic of unbounded orders, has
each element in a homomorphic image of (∏ ℤ)/U but is not a homomorphic image of any nonprincipal
ultraproduct (∏ Gᵢ)/V; Kourovka Notebook (21st issue), Problem 21.12: No, it need not,
https://arxiv.org/abs/2503.09228.
-/
public theorem_wanted locallyUltrapowerImageIsUltraproductImage_refuted :
    ¬ locallyUltrapowerImageIsUltraproductImage

end MathlibExt.GroupTheory.UltraproductImageKourovka21Problem12Wanted

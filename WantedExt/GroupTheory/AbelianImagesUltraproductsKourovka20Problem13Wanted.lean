/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Abelian images of ultraproducts and products (Kourovka Notebook Problem 20.13)

Kourovka Notebook, Problem 20.13 (G. M. Bergman), marked solved in the 21st issue: (a) if an abelian
group can be written as a homomorphic image of a nonprincipal countable ultraproduct of not
necessarily abelian groups `Gᵢ`, must it be a homomorphic image of a nonprincipal countable
ultraproduct of abelian groups? (b) If an abelian group can be written as a homomorphic image of a
direct product of an infinite family of not necessarily abelian finite groups, can it be written as
a homomorphic image of a direct product of finite abelian groups?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Ultrafilter.Defs

@[expose] public section

namespace MathlibExt.GroupTheory.AbelianImagesUltraproductsKourovka20Problem13Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 20.13 (G. M. Bergman). UnsolvedMath record
UM-00701671 (`KOU-20.13`), dataset ulamai/UnsolvedMath v1.8.0.

A countable ultraproduct is indexed by `ℕ`: `(∏ᵢ Gᵢ)/U`, the quotient by the normal subgroup of
sequences equal to `1` on a set in `U`, with `U` nonprincipal: `(U : Filter ℕ) ≤ Filter.cofinite`,
i.e. every cofinite set lies in `U` (Mathlib orders filters by reverse inclusion;
`Filter.hyperfilter` is such an ultrafilter). In (a) the abelian family and its ultrafilter may be
chosen afresh; in (b) the family of finite abelian groups is indexed by any type.
-/

/-- The normal subgroup of sequences that are `1` on a set in the ultrafilter `U`. -/
abbrev ultraproductKernel (U : Ultrafilter ℕ) (G : ℕ → Type) [∀ i, Group (G i)] :
    Subgroup (∀ i, G i) :=
  Subgroup.normalClosure {f | ∀ᶠ i in (U : Filter ℕ), f i = 1}

/-- The ultraproduct `(∏ i, G i) / U` of a countable family of groups. -/
abbrev Ultraproduct (U : Ultrafilter ℕ) (G : ℕ → Type) [∀ i, Group (G i)] : Type :=
  (∀ i, G i) ⧸ ultraproductKernel U G

/-- Kourovka 20.13(a) (G. M. Bergman): an abelian group that is a homomorphic image of a
nonprincipal ultraproduct of a countable family of (not necessarily abelian) groups is a
homomorphic image of a nonprincipal ultraproduct of a countable family of abelian groups. -/
def abelianImageOfUltraproductIsImageOfAbelianUltraproduct : Prop :=
  ∀ (A : Type) [CommGroup A] (G : ℕ → Type) [∀ i, Group (G i)] (U : Ultrafilter ℕ),
    (U : Filter ℕ) ≤ Filter.cofinite →
    (∃ φ : Ultraproduct U G →* A, Function.Surjective φ) →
    ∃ (H : ℕ → Type) (_ : ∀ i, CommGroup (H i)) (V : Ultrafilter ℕ),
      (V : Filter ℕ) ≤ Filter.cofinite ∧ ∃ ψ : Ultraproduct V H →* A, Function.Surjective ψ

/-- Kourovka 20.13(b): an abelian group that is a homomorphic image of the direct product of an
infinite family of finite (not necessarily abelian) groups is a homomorphic image of a direct
product of finite abelian groups. -/
def abelianImageOfProductOfFiniteIsImageOfAbelianProduct : Prop :=
  ∀ (A : Type) [CommGroup A] (I : Type) [Infinite I] (G : I → Type) [∀ i, Group (G i)]
    [∀ i, Finite (G i)], (∃ φ : (∀ i, G i) →* A, Function.Surjective φ) →
    ∃ (J : Type) (H : J → Type) (_ : ∀ j, CommGroup (H j)), (∀ j, Finite (H j)) ∧
      ∃ ψ : (∀ j, H j) →* A, Function.Surjective ψ

/--
Resolved true: Corson (2025) answers 20.13(a) affirmatively: an abelian image of `(∏ᵢ Gᵢ)/U` is an
image of `(∏ᵢ Gᵢ)/(⊕ᵢ Gᵢ)`, hence cotorsion (Theorem 17, (2) ⇒ (1)), hence an image of a
nonprincipal ultraproduct of abelian groups (Proposition 10, (i) ⇒ (iv)); the Kourovka Notebook
(21st issue) marks 20.13 solved. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems
in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 20.13 (G. M.
Bergman); resolution: S. M. Corson, On homomorphic images of ultraproducts, preprint,
arXiv:2503.09228 (2025), Theorem 17 with Proposition 10: an abelian group is cotorsion iff it is an
image of (∏ G_i)/(⊕ G_i) for some sequence of groups, iff an image of a product of finite cyclic
groups, iff an image of a product of finite groups, and cotorsion groups are images of nonprincipal
ultraproducts of abelian groups; Questions 1 and 2 (Kourovka 20.13(a), (b)) are answered
affirmatively, https://arxiv.org/abs/2503.09228.
-/
public theorem_wanted abelianImageOfUltraproductIsImageOfAbelianUltraproduct_holds :
    abelianImageOfUltraproductIsImageOfAbelianUltraproduct

/--
Resolved true: Corson (2025) answers 20.13(b) affirmatively: an abelian image of a direct product of
finite groups is an image of a direct product of finite cyclic groups (Theorem 17, (4) ⇒ (3)); the
Kourovka Notebook (21st issue) marks 20.13 solved. Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Problem 20.13 (G. M. Bergman); resolution: S. M. Corson, On homomorphic images of ultraproducts,
preprint, arXiv:2503.09228 (2025), Theorem 17 with Proposition 10: an abelian group is cotorsion iff
it is an image of (∏ G_i)/(⊕ G_i) for some sequence of groups, iff an image of a product of finite
cyclic groups, iff an image of a product of finite groups, and cotorsion groups are images of
nonprincipal ultraproducts of abelian groups; Questions 1 and 2 (Kourovka 20.13(a), (b)) are
answered affirmatively, https://arxiv.org/abs/2503.09228.
-/
public theorem_wanted abelianImageOfProductOfFiniteIsImageOfAbelianProduct_holds :
    abelianImageOfProductOfFiniteIsImageOfAbelianProduct

end MathlibExt.GroupTheory.AbelianImagesUltraproductsKourovka20Problem13Wanted

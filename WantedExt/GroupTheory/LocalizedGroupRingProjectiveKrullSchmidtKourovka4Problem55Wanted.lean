/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Non-unique decompositions of projective Z_(p)G-modules (Kourovka Notebook Problem 4.55)

Kourovka Notebook, Problem 4.55 (K. W. Roggenkamp), marked solved in the 21st issue: let `G` be a
finite group, and `ℤ_(p)` the localization at `p`. Can every projective `ℤ_(p)G`-module be uniquely,
up to permutations and isomorphisms, written as a direct sum of indecomposable projective
`ℤ_(p)G`-modules? It is known that the category of finitely generated projective `ℤ_(p)G`-modules is
not a Krull-Schmidt category (S. M. Woods, Canadian J. Math. 26 (1974), 121-129).
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.LocalizedGroupRingProjectiveKrullSchmidtKourovka4Problem55Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 4.55 (K. W. Roggenkamp). UnsolvedMath
record UM-00700262 (`KOU-4.55`), dataset ulamai/UnsolvedMath v1.8.0.

`ℤ_(p)` is `Localization.AtPrime (Ideal.span {p})` and `ℤ_(p)G` its group ring (`MonoidAlgebra`).
Indecomposable means non-zero and not the direct sum of two non-zero submodules; a decomposition is
a family of indecomposable projective submodules whose internal direct sum is the module
(`DirectSum.IsInternal`), and uniqueness matches any two decompositions by a bijection of the index
sets with isomorphic corresponding summands. The claim is stated for finitely generated projective
modules, where the counterexample lives; its refutation implies the refutation of the claim for all
projective modules.
-/

/-- The `R`-module `M` is indecomposable: non-zero and not the direct sum of two non-zero
submodules. -/
def IsIndecomposable (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] : Prop :=
  Nontrivial M ∧ ∀ P Q : Submodule R M, IsCompl P Q → P = ⊥ ∨ Q = ⊥

/-- The family `N` of submodules of `M` decomposes `M` into indecomposable projective summands:
`M` is the internal direct sum of the `N i`, each indecomposable and projective. -/
def IsProjectiveDecomposition {R M ι : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [DecidableEq ι] (N : ι → Submodule R M) : Prop :=
  DirectSum.IsInternal N ∧ ∀ i, IsIndecomposable R (N i) ∧ Module.Projective R (N i)

/-- `M` is uniquely, up to permutation and isomorphism of the summands, a direct sum of
indecomposable projective submodules: such a decomposition exists, and any two are matched by a
bijection of the index sets under which corresponding summands are isomorphic. -/
def HasUniqueProjectiveDecomposition (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] :
    Prop :=
  (∃ (ι : Type) (_ : DecidableEq ι) (N : ι → Submodule R M), IsProjectiveDecomposition N) ∧
    ∀ (ι κ : Type) [DecidableEq ι] [DecidableEq κ] (N : ι → Submodule R M)
      (N' : κ → Submodule R M), IsProjectiveDecomposition N → IsProjectiveDecomposition N' →
      ∃ e : ι ≃ κ, ∀ i, Nonempty (N i ≃ₗ[R] N' (e i))

/-- Kourovka 4.55 (K. W. Roggenkamp), for finitely generated modules: for every finite group `G`
and prime `p`, every finitely generated projective `ℤ_(p)G`-module is uniquely, up to permutations
and isomorphisms, a direct sum of indecomposable projective `ℤ_(p)G`-modules. Here `ℤ_(p)` is the
localization of `ℤ` at the prime ideal `(p)` and `ℤ_(p)G` its group ring. -/
def finitelyGeneratedProjectivesUniquelyDecomposable : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [(Ideal.span {(p : ℤ)}).IsPrime], p.Prime →
    ∀ (M : Type) [AddCommGroup M]
      [Module (MonoidAlgebra (Localization.AtPrime (Ideal.span {(p : ℤ)})) G) M],
      Module.Projective (MonoidAlgebra (Localization.AtPrime (Ideal.span {(p : ℤ)})) G) M →
      Module.Finite (MonoidAlgebra (Localization.AtPrime (Ideal.span {(p : ℤ)})) G) M →
      HasUniqueProjectiveDecomposition
        (MonoidAlgebra (Localization.AtPrime (Ideal.span {(p : ℤ)})) G) M

/--
Resolved false: Jayadevan constructs finitely generated indecomposable projective
`ℤ_(11)PSL₂(𝔽₁₁)`-modules `A, B, C, D` with `A ⊕ D ≅ B ⊕ C`, `A ≇ B` and `A ≇ C`, so `A ⊕ D` has two
inequivalent decompositions into indecomposable projectives. The solution is AI-generated and was
confirmed by D. Rumynin; the 21st issue of the Kourovka Notebook marks 4.55 solved ("No, not
every"). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 4.55 (K. W. Roggenkamp);
resolution: A. Jayadevan, Nonunique indecomposable projective decompositions over the localized
group ring of PSL2(F11), preprint, Zenodo record 22750727 (2026), abstract: for `O = ℤ_(11)` and `G
= PSL₂(𝔽₁₁)`, nonzero finitely generated indecomposable projective `O[G]`-modules `A, B, C, D` of
`O`-rank `44` with `A ⊕ D ≅ B ⊕ C`, `A ≇ B`, `A ≇ C`, so a projective module of rank `88` has two
inequivalent decompositions into indecomposable projectives; an AI solution confirmed by D. Rumynin,
which the Kourovka Notebook (21st issue) accepts: No, not every,
https://zenodo.org/records/22750727.
-/
public theorem_wanted finitelyGeneratedProjectivesUniquelyDecomposable_refuted :
    ¬ finitelyGeneratedProjectivesUniquelyDecomposable

end MathlibExt.GroupTheory.LocalizedGroupRingProjectiveKrullSchmidtKourovka4Problem55Wanted

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Eigenvalues of representation operators are roots of unity

For a finite group `G` and a finite-dimensional complex representation `ρ`,
every eigenvalue `μ` of `ρ g` satisfies `μ ^ orderOf g = 1`, hence also
`μ ^ Fintype.card G = 1`: `ρ g` has finite order, so its minimal polynomial
divides `X ^ orderOf g - 1`. In particular, every root of the characteristic
polynomial of (the matrix of) `ρ g` is a `|G|`-th root of unity.

Proof idea: `ρ g` is annihilated by `X ^ orderOf g - 1`, so the minimal
polynomial of `ρ g` divides it; an eigenvalue is a root of the minimal
polynomial, hence a root of `X ^ orderOf g - 1`. The `|G|` version follows
since `orderOf g` divides `|G|`.

Source: `v1/Atlas/AlgebraNotes/code/Characters.lean` (theorem
`CharacterTheory.char_charpoly_roots_pow_eq_one`). The eigenvalue form
`hasEigenvalue_pow_orderOf_eq_one` is the sharper version of the same
argument, with the `|G|` form as a corollary. Mathlib has the related
integrality statement `Representation.isIntegral_character` (character
values are algebraic integers) but no statement that the eigenvalues, or
the roots of the characteristic polynomial, of `ρ g` are roots of unity.
This complements `CharacterTheory.char_inv_eq_conj` (Batch 11), whose
proof uses the same eigenvalue fact inline.
-/

@[expose] public section

namespace CharacterTheory

universe u

/-- **Eigenvalues of $\rho(g)$ are roots of unity of order dividing that of $g$.** Let $\rho$ be a
representation of a finite group $G$ on a finite-dimensional complex vector space $V$, let
$g \in G$, and let $\operatorname{ord}(g)$ be the order of $g$. Every eigenvalue $\mu$ of $\rho(g)$
satisfies $\mu^{\operatorname{ord}(g)} = 1$.

The minimal polynomial of $\rho(g)$ divides $X^{\operatorname{ord}(g)} - 1$, and $\mu$ is a root of
the minimal polynomial. -/
theorem hasEigenvalue_pow_orderOf_eq_one
    {G : Type u} [Group G] [Fintype G]
    {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (ρ g) μ) :
    μ ^ orderOf g = 1 := by
  have hord : (ρ g) ^ orderOf g = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hev_minpoly : (minpoly ℂ (ρ g)).IsRoot μ :=
    Module.End.hasEigenvalue_iff_isRoot.mp hμ
  have hdvd : minpoly ℂ (ρ g) ∣ (Polynomial.X ^ orderOf g - 1) := by
    apply minpoly.dvd
    simp only [map_sub, map_pow, map_one, Polynomial.aeval_X]
    exact sub_eq_zero.mpr hord
  have hμ_root : (Polynomial.X ^ orderOf g - 1 : Polynomial ℂ).IsRoot μ := by
    obtain ⟨r, hr⟩ := hdvd
    rw [Polynomial.IsRoot.def] at hev_minpoly ⊢
    rw [hr, Polynomial.eval_mul, hev_minpoly, zero_mul]
  simp only [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_one] at hμ_root
  exact sub_eq_zero.mp hμ_root

/-- **Eigenvalues of $\rho(g)$ are $|G|$-th roots of unity.** Let $\rho$ be a representation of a
finite group $G$ on a finite-dimensional complex vector space $V$, and let $g \in G$. Every
eigenvalue $\mu$ of $\rho(g)$ satisfies $\mu^{|G|} = 1$.

This follows because the order of $g$ divides $|G|$. -/
theorem hasEigenvalue_pow_card_eq_one
    {G : Type u} [Group G] [Fintype G]
    {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (ρ g) μ) :
    μ ^ Fintype.card G = 1 := by
  obtain ⟨k, hk⟩ := orderOf_dvd_card (x := g)
  rw [hk, pow_mul, hasEigenvalue_pow_orderOf_eq_one ρ g hμ, one_pow]

/-- **Characteristic roots of $\rho(g)$ are $|G|$-th roots of unity.** Let $\rho$ be a
representation of a finite group $G$ on a finite-dimensional complex vector space $V$, and let
$g \in G$. Every root $\mu$ of the characteristic polynomial of the matrix of $\rho(g)$ in a fixed
basis of $V$ satisfies $\mu^{|G|} = 1$. -/
theorem char_charpoly_roots_pow_eq_one
    {G : Type u} [Group G] [Fintype G]
    {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    ∀ μ ∈ ((LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V)
      (ρ g)).charpoly.roots), μ ^ Fintype.card G = 1 := by
  intro μ hμ
  have hev : Module.End.HasEigenvalue (ρ g) μ := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly,
      ← LinearMap.charpoly_toMatrix (ρ g) (Module.finBasis ℂ V)]
    exact (Polynomial.mem_roots ((Matrix.charpoly_monic _).ne_zero)).mp hμ
  exact hasEigenvalue_pow_card_eq_one ρ g hev

end CharacterTheory

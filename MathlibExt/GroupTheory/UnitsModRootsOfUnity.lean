/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Torsion
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Homomorphisms from a finite group to the units modulo the roots of unity

For a field `K`, the roots of unity of `K` form the torsion subgroup `CommGroup.torsion Kˣ` of
`Kˣ`: a unit `u` lies in it exactly when `u ∈ rootsOfUnity n K` for some `n ≥ 1`
(`mem_torsion_units_iff_exists_mem_rootsOfUnity`). Mathlib shows that the quotient of a
commutative group by its torsion subgroup is torsion free (`QuotientGroup.instHasUniqueRoots`
and `instIsMulTorsionFreeOfHasUniqueRoots`). This module deduces the statement Pazuki uses in the
proof of Proposition 5.1 of *Theta height and Faltings height*: every group homomorphism from a
finite group to `Kˣ ⧸ CommGroup.torsion Kˣ` is trivial.

* `MonoidHom.eq_one_of_finite_of_isMulTorsionFree`: a homomorphism from a finite group to a
  torsion-free group is trivial;
* `units_quotient_torsion_isMulTorsionFree_and_eq_one`: the statement of the page, both parts.
-/

public section

/-- A unit $u$ of a field $K$ lies in the torsion subgroup of $K^\times$ exactly when it is a root
of unity: $u \in \mu_n(K)$ for some integer $n \ge 1$. So `CommGroup.torsion Kˣ` is the group
$\mu_\infty(K)$ of roots of unity in $K$. -/
theorem mem_torsion_units_iff_exists_mem_rootsOfUnity {K : Type*} [Field K] (u : Kˣ) :
    u ∈ CommGroup.torsion Kˣ ↔ ∃ n : ℕ, 0 < n ∧ u ∈ rootsOfUnity n K := by
  rw [CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
  simp only [mem_rootsOfUnity]

/-- A group homomorphism $f$ from a finite group $G$ to a torsion-free group $H$ is trivial: the
image $f(x)$ of every $x \in G$ has finite order, so it is $1$. -/
theorem MonoidHom.eq_one_of_finite_of_isMulTorsionFree {G H : Type*} [Group G] [Finite G]
    [Group H] [IsMulTorsionFree H] (f : G →* H) : f = 1 := by
  ext x
  by_contra hx
  exact (isMulTorsionFree_iff_not_isOfFinOrder.mp inferInstance) hx
    (f.isOfFinOrder (isOfFinOrder_of_finite x))

/-- **Homomorphisms from a finite group to the units modulo the roots of unity.** Let $K$ be a
field and $\mu_\infty(K)$ the group of roots of unity in $K$, here `CommGroup.torsion Kˣ` (see
`mem_torsion_units_iff_exists_mem_rootsOfUnity`). Then the group $K^\times / \mu_\infty(K)$ is
torsion free, and every group homomorphism from a finite group to $K^\times / \mu_\infty(K)$ is
trivial.

Source: F. Pazuki, *Theta height and Faltings height*, Bull. Soc. Math. France 140 (2012), 19–49,
<https://doi.org/10.24033/bsmf.2623>, the proof of Proposition 5.1, p. 39 (arXiv:0907.1458v2,
p. 17), where $x \mapsto [\lambda_x]$ is a morphism from the finite abelian group $A_{r^2}(K)$ to
the torsion-free group $K^\star / \mu_\infty(K)$. -/
theorem units_quotient_torsion_isMulTorsionFree_and_eq_one (K : Type*) [Field K] :
    IsMulTorsionFree (Kˣ ⧸ CommGroup.torsion Kˣ) ∧
      ∀ (G : Type*) [Group G] [Finite G] (f : G →* Kˣ ⧸ CommGroup.torsion Kˣ), f = 1 :=
  ⟨inferInstance, fun _ _ _ f ↦ f.eq_one_of_finite_of_isMulTorsionFree⟩

/-- Every group homomorphism from a finite group to $K^\times / \mu_\infty(K)$, for a field $K$,
is trivial.

Source: F. Pazuki, *Theta height and Faltings height*, Bull. Soc. Math. France 140 (2012), 19–49,
<https://doi.org/10.24033/bsmf.2623>, the proof of Proposition 5.1, p. 39 (arXiv:0907.1458v2,
p. 17). -/
theorem MonoidHom.eq_one_of_finite_to_units_quotient_torsion {K : Type*} [Field K] {G : Type*}
    [Group G] [Finite G] (f : G →* Kˣ ⧸ CommGroup.torsion Kˣ) : f = 1 :=
  f.eq_one_of_finite_of_isMulTorsionFree

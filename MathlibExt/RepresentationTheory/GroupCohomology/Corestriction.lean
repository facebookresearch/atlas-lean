/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_GroupCohomology_Corestriction2.lean`,
`Theorems/Thm_groupCohomology_Cores_cores_eq_cores.lean`
and
`P2M/Sol/S_groupCohomology_Cores_cores_eq_cores.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Corestriction in degree two

Let `H ≤ G` be a subgroup of finite index and `A` a representation of `G`. A transversal `τ` of
the left cosets `G ⧸ H` gives explicit corestriction maps `cor₁` and `cor₂` on 1- and 2-cochains.
They preserve cocycles and coboundaries, hence induce the corestriction
`cores A τ : H²(H, A) → H²(G, A)`. Changing the transversal changes `cor₂` of a 2-cocycle by a
2-coboundary, so `cores A τ` does not depend on `τ` (`cores_eq_cores`).
-/

@[expose] public section

open CategoryTheory groupCohomology

namespace groupCohomology

universe u
namespace Cores

section Transversal
variable {G : Type*} [Group G] (H : Subgroup G)

/-- **Transversal of the left cosets.** A transversal of the left cosets `gH` of a subgroup
`H ≤ G`: a representative `σ q ∈ q` of each coset `q : G ⧸ H`, with the coset `H` represented
by `1`. The inverses `(σ q)⁻¹` then represent the right cosets `Hg`, one each: the right coset
`Hx` is represented by `(σ (x⁻¹H))⁻¹`. -/
structure Transversal where
  /-- The representative of each left coset. -/
  σ : G ⧸ H → G
  /-- Each representative lies in its coset. -/
  mk_σ : ∀ q, (σ q : G ⧸ H) = q
  /-- The coset `H` is represented by `1`. -/
  σ_one : σ ((1 : G) : G ⧸ H) = 1

namespace Transversal
variable {H}

/-- **Transversals exist.** Every subgroup `H ≤ G` has a transversal of its left cosets with
the coset `H` represented by `1`. -/
lemma nonempty : Nonempty (Transversal H) := by
  classical
  refine ⟨⟨Function.update Quotient.out ((1 : G) : G ⧸ H) 1, fun q => ?_,
    Function.update_self _ _ _⟩⟩
  by_cases hq : q = ((1 : G) : G ⧸ H)
  · subst hq; rw [Function.update_self]
  · rw [Function.update_of_ne hq]; exact q.out_eq

variable (τ : Transversal H)

/-- **Left coset of the inverse.** For a subgroup `H ≤ G` and `x : G`, the left coset `x⁻¹H`
of `x⁻¹`. -/
abbrev qinv (x : G) : G ⧸ H := ((x⁻¹ : G) : G ⧸ H)

lemma lam_mem (x : G) : x * τ.σ (qinv (H := H) x) ∈ H := by
  have h : ((τ.σ (qinv (H := H) x) : G) : G ⧸ H) = ((x⁻¹ : G) : G ⧸ H) := τ.mk_σ _
  rw [QuotientGroup.eq] at h
  have := H.inv_mem h
  rwa [mul_inv_rev, inv_inv, inv_inv] at this

/-- **The `H`-component for a transversal.** For a transversal `τ` of the left cosets of `H`
and `x : G`, the element `τ.lam x = x * σ (x⁻¹H)` of `H`. It satisfies
`x = τ.lam x * (σ (x⁻¹H))⁻¹`, so it is the `H`-component of `x` for the right transversal
formed by the inverses `(σ q)⁻¹`. -/
def lam (x : G) : H := ⟨x * τ.σ (qinv (H := H) x), τ.lam_mem x⟩

lemma coe_lam (x : G) : (τ.lam x : G) = x * τ.σ (qinv (H := H) x) := rfl

lemma lam_mul_σ_inv (x : G) :
    (τ.lam x : G) * (τ.σ (qinv (H := H) x))⁻¹ = x := by
  rw [coe_lam, mul_inv_cancel_right]

lemma qinv_eq_of_eq {y μ : G} (hμ : μ ∈ H) {q : G ⧸ H}
    (h : y = μ * (τ.σ q)⁻¹) : qinv (H := H) y = q := by
  rw [qinv, ← τ.mk_σ q, QuotientGroup.eq, inv_inv, h, mul_assoc, inv_mul_cancel, mul_one]; exact hμ

lemma coe_lam_eq_of_eq {y μ : G} (hμ : μ ∈ H) {q : G ⧸ H}
    (h : y = μ * (τ.σ q)⁻¹) : (τ.lam y : G) = μ := by
  rw [coe_lam, τ.qinv_eq_of_eq hμ h, h, inv_mul_cancel_right]

lemma coe_lam_of_mem {s : G} (hs : s ∈ H) : (τ.lam s : G) = s :=
  τ.coe_lam_eq_of_eq hs (q := ((1 : G) : G ⧸ H)) (by rw [τ.σ_one, inv_one, mul_one])

lemma coe_lam_σ_inv (q : G ⧸ H) : (τ.lam (τ.σ q)⁻¹ : G) = 1 :=
  τ.coe_lam_eq_of_eq H.one_mem (by rw [one_mul])

lemma qinv_σ_inv (q : G ⧸ H) : qinv (H := H) (τ.σ q)⁻¹ = q :=
  τ.qinv_eq_of_eq H.one_mem (by rw [one_mul])

lemma coe_lam_mul (x g : G) :
    (τ.lam (x * g) : G) = τ.lam x * τ.lam ((τ.σ (qinv (H := H) x))⁻¹ * g) := by
  apply τ.coe_lam_eq_of_eq (H.mul_mem (τ.lam x).2 (τ.lam _).2)
    (q := qinv (H := H) ((τ.σ (qinv (H := H) x))⁻¹ * g))
  conv_lhs => rw [← τ.lam_mul_σ_inv x, mul_assoc, ← τ.lam_mul_σ_inv ((τ.σ (qinv (H := H) x))⁻¹ * g)]
  rw [mul_assoc]

lemma lam_mul (x g : G) :
    τ.lam (x * g) = τ.lam x * τ.lam ((τ.σ (qinv (H := H) x))⁻¹ * g) :=
  Subtype.ext (τ.coe_lam_mul x g)

lemma qinv_σ_inv_mul (q : G ⧸ H) (g : G) : qinv (H := H) ((τ.σ q)⁻¹ * g) = g⁻¹ • q := by
  rw [qinv, mul_inv_rev, inv_inv]
  conv_rhs => rw [← τ.mk_σ q]
  rfl

lemma mul_σ (q : G ⧸ H) (g : G) : g * τ.σ (g⁻¹ • q) = τ.σ q * (τ.lam ((τ.σ q)⁻¹ * g) : G) := by
  have hσ : (τ.σ (qinv (H := H) ((τ.σ q)⁻¹ * g)))⁻¹ = (τ.σ (g⁻¹ • q))⁻¹ := by rw [qinv_σ_inv_mul]
  have h1 := τ.lam_mul_σ_inv ((τ.σ q)⁻¹ * g)
  rw [hσ] at h1
  calc g * τ.σ (g⁻¹ • q) = τ.σ q * ((τ.σ q)⁻¹ * g) * τ.σ (g⁻¹ • q) := by group
    _ = τ.σ q * ((τ.lam ((τ.σ q)⁻¹ * g) : G) * (τ.σ (g⁻¹ • q))⁻¹) * τ.σ (g⁻¹ • q) := by rw [h1]
    _ = τ.σ q * (τ.lam ((τ.σ q)⁻¹ * g) : G) := by group

lemma lam_of_mem (s : H) : τ.lam (s : G) = s := Subtype.ext (τ.coe_lam_of_mem s.2)

private lemma lam_mul_left (h : H) (y : G) : τ.lam ((h : G) * y) = h * τ.lam y := by
  have h1 : qinv (H := H) (h : G) = ((1 : G) : G ⧸ H) := by
    rw [qinv, QuotientGroup.eq, inv_inv, mul_one]; exact h.2
  rw [τ.lam_mul, τ.lam_of_mem, h1, τ.σ_one, inv_one, one_mul]

private lemma lam_σ_inv (q : G ⧸ H) : τ.lam (τ.σ q)⁻¹ = 1 :=
  Subtype.ext (by rw [τ.coe_lam_σ_inv, Subgroup.coe_one])

end Transversal
end Transversal

section Homog
variable {k G : Type u} [CommRing k] [Group G] {H : Subgroup G} (A : Rep k G)

/-- The homogeneous form `(a, b, c) ↦ a • u (a⁻¹ * b, b⁻¹ * c)` of a 2-cochain `u` of `H`. -/
private noncomputable def homog (u : H × H → A) (a b c : H) : A :=
  A.ρ (a : G) (u (a⁻¹ * b, b⁻¹ * c))

private lemma homog_one (u : H × H → A) (b c : H) : homog A u 1 b c = u (b, b⁻¹ * c) := by
  rw [homog, inv_one, one_mul, Subgroup.coe_one, map_one, one_apply_eq_self]

private lemma homog_mul (u : H × H → A) (h a b c : H) :
    homog A u (h * a) (h * b) (h * c) = A.ρ (h : G) (homog A u a b c) := by
  rw [homog, homog, mul_inv_rev, mul_assoc, inv_mul_cancel_left, mul_inv_rev, mul_assoc,
    inv_mul_cancel_left, Subgroup.coe_mul, map_mul, mul_apply_eq_comp]

/-- The homogeneous form of a 2-cocycle satisfies the homogeneous cocycle identity. -/
private lemma homog_cocycle {u : H × H → A} (hu : u ∈ cocycles₂ (Rep.res H.subtype A))
    (a b c d : H) :
    homog A u b c d - homog A u a c d + homog A u a b d - homog A u a b c = 0 := by
  have key := (mem_cocycles₂_def (A := Rep.res H.subtype A) u).1 hu
    (a⁻¹ * b) (b⁻¹ * c) (c⁻¹ * d)
  have e1 : a⁻¹ * b * (b⁻¹ * c) = a⁻¹ * c := by group
  have e2 : b⁻¹ * c * (c⁻¹ * d) = b⁻¹ * d := by group
  rw [e1, e2] at key
  have hb : homog A u b c d =
      A.ρ (a : G) ((Rep.res H.subtype A).ρ (a⁻¹ * b) (u (b⁻¹ * c, c⁻¹ * d))) := by
    rw [homog, Rep.coe_res_obj_ρ', ← mul_apply_eq_comp, ← map_mul, H.coe_subtype,
      ← Subgroup.coe_mul, mul_inv_cancel_left]
  rw [hb, homog, homog, homog, ← map_sub, ← map_add, ← map_sub, key, map_zero]

/-- The prism decomposition: for a function `U` satisfying the homogeneous cocycle identity and
two maps `η η'`, the difference of `U` along `η'` and along `η` is an alternating sum of three
prism terms. -/
private lemma prism {X : Type*} (U : H → H → H → A)
    (hU : ∀ a b c d : H, U b c d - U a c d + U a b d - U a b c = 0)
    (η η' : X → H) (z₀ z₁ z₂ : X) :
    U (η' z₀) (η' z₁) (η' z₂) - U (η z₀) (η z₁) (η z₂) =
      (U (η z₁) (η' z₁) (η' z₂) - U (η z₁) (η z₂) (η' z₂)) -
        (U (η z₀) (η' z₀) (η' z₂) - U (η z₀) (η z₂) (η' z₂)) +
        (U (η z₀) (η' z₀) (η' z₁) - U (η z₀) (η z₁) (η' z₁)) := by
  have h1 := hU (η z₀) (η' z₀) (η' z₁) (η' z₂)
  have h2 := hU (η z₀) (η z₁) (η' z₁) (η' z₂)
  have h3 := hU (η z₀) (η z₁) (η z₂) (η' z₂)
  linear_combination (norm := abel) h1 - h2 + h3

/-- The prism term attached to two maps `η η' : G → H` and a 2-cochain `u` of `H`. -/
private noncomputable def W (η η' : G → H) (u : H × H → A) (y₀ y₁ : G) : A :=
  homog A u (η y₀) (η' y₀) (η' y₁) - homog A u (η y₀) (η y₁) (η' y₁)

private lemma W_mul (η η' : G → H) (hη : ∀ (h : H) (y : G), η (h * y) = h * η y)
    (hη' : ∀ (h : H) (y : G), η' (h * y) = h * η' y) (u : H × H → A) (h : H) (y₀ y₁ : G) :
    W A η η' u (h * y₀) (h * y₁) = A.ρ (h : G) (W A η η' u y₀ y₁) := by
  rw [W, W, hη, hη', hη', hη, homog_mul, homog_mul, map_sub]

end Homog

section Cor
variable {k G : Type u} [CommRing k] [Group G] {H : Subgroup G} [H.FiniteIndex]
  (A : Rep k G) (τ : Transversal H)

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- **Corestriction of 1-cochains.** For a subgroup `H` of finite index, a representation `A` of
`G` and a transversal `τ` of the left cosets of `H`, the 1-cochain of `G` given by
`cor₁ u g = ∑ q : G ⧸ H, ρ (σ q) (u (τ.lam ((σ q)⁻¹ * g)))` for a 1-cochain `u` of `H`, where
`ρ` is the action of `G` on `A`. -/
noncomputable def cor₁ (u : H → A) : G → A := fun g =>
  ∑ q : G ⧸ H, A.ρ (τ.σ q) (u (τ.lam ((τ.σ q)⁻¹ * g)))

/-- **Corestriction of 2-cochains.** For a subgroup `H` of finite index, a representation `A` of
`G` and a transversal `τ` of the left cosets of `H`, the 2-cochain of `G` given by
`cor₂ u (g₁, g₂) = ∑ q : G ⧸ H, ρ (σ q) (u (h₁, h₁⁻¹ * τ.lam ((σ q)⁻¹ * g₁ * g₂)))` for a
2-cochain `u` of `H`, where `h₁ = τ.lam ((σ q)⁻¹ * g₁)` and `ρ` is the action of `G` on `A`.
The second argument of `u` equals `τ.lam ((σ (g₁⁻¹ • q))⁻¹ * g₂)`. -/
noncomputable def cor₂ (u : H × H → A) : G × G → A := fun gg =>
  ∑ q : G ⧸ H, A.ρ (τ.σ q) (u (τ.lam ((τ.σ q)⁻¹ * gg.1),
    (τ.lam ((τ.σ q)⁻¹ * gg.1))⁻¹ * τ.lam ((τ.σ q)⁻¹ * gg.1 * gg.2)))

lemma cor₂_apply (u : H × H → A) (g₁ g₂ : G) : cor₂ A τ u (g₁, g₂) =
    ∑ q : G ⧸ H, A.ρ (τ.σ q) (u (τ.lam ((τ.σ q)⁻¹ * g₁),
      (τ.lam ((τ.σ q)⁻¹ * g₁))⁻¹ * τ.lam ((τ.σ q)⁻¹ * g₁ * g₂))) := rfl

lemma cor₁_apply (u : H → A) (g : G) :
    cor₁ A τ u g = ∑ q : G ⧸ H, A.ρ (τ.σ q) (u (τ.lam ((τ.σ q)⁻¹ * g))) := rfl

theorem cor₂_d₁₂ (u : H → A) :
    cor₂ A τ ((d₁₂ (Rep.res H.subtype A)).hom u) = (d₁₂ A).hom (cor₁ A τ u) := by
  funext gh
  obtain ⟨g, h⟩ := gh
  rw [d₁₂_hom_apply, cor₂_apply, cor₁_apply, cor₁_apply, cor₁_apply, map_sum]
  have hre : ∑ q : G ⧸ H, A.ρ g (A.ρ (τ.σ q) (u (τ.lam ((τ.σ q)⁻¹ * h)))) =
      ∑ q : G ⧸ H, A.ρ g (A.ρ (τ.σ (g⁻¹ • q)) (u (τ.lam ((τ.σ (g⁻¹ • q))⁻¹ * h)))) :=
    (Fintype.sum_equiv (MulAction.toPerm g⁻¹) _ _ fun q => rfl).symm
  dsimp only
  rw [hre, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  set x : G := (τ.σ q)⁻¹ with hx
  set x' : G := (τ.σ (g⁻¹ • q))⁻¹ with hx'
  have hσ : (τ.σ (Transversal.qinv (H := H) (x * g)))⁻¹ = x' := by
    rw [hx, Transversal.qinv_σ_inv_mul, ← hx']
  have hab : τ.lam (x * g * h) = τ.lam (x * g) * τ.lam (x' * h) := by rw [τ.lam_mul (x * g) h, hσ]
  have hgσ : A.ρ g * A.ρ (τ.σ (g⁻¹ • q)) = A.ρ (τ.σ q) * A.ρ ((τ.lam (x * g) : H) : G) := by
    rw [← map_mul, ← map_mul, hx]; exact congrArg _ (τ.mul_σ q g)
  rw [show x * (g * h) = x * g * h from (mul_assoc _ _ _).symm, hab, inv_mul_cancel_left,
    d₁₂_hom_apply,
    ← mul_apply_eq_comp, hgσ, mul_apply_eq_comp, ← map_sub, ← map_add]
  rfl

theorem cor₂_mem_cocycles₂ {u : H × H → A}
    (hu : u ∈ cocycles₂ (Rep.res H.subtype A)) : cor₂ A τ u ∈ cocycles₂ A := by
  rw [mem_cocycles₂_iff] at hu ⊢
  intro g h j
  simp only [cor₂_apply]
  rw [map_sum]
  have hre : ∑ q : G ⧸ H, A.ρ g (A.ρ (τ.σ q) (u (τ.lam ((τ.σ q)⁻¹ * h),
    (τ.lam ((τ.σ q)⁻¹ * h))⁻¹ * τ.lam ((τ.σ q)⁻¹ * h * j)))) =
      ∑ q : G ⧸ H, A.ρ g (A.ρ (τ.σ (g⁻¹ • q)) (u (τ.lam ((τ.σ (g⁻¹ • q))⁻¹ * h),
        (τ.lam ((τ.σ (g⁻¹ • q))⁻¹ * h))⁻¹ * τ.lam ((τ.σ (g⁻¹ • q))⁻¹ * h * j)))) :=
    (Fintype.sum_equiv (MulAction.toPerm g⁻¹) _ _ fun q => rfl).symm
  rw [hre, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  set x : G := (τ.σ q)⁻¹ with hx
  set x' : G := (τ.σ (g⁻¹ • q))⁻¹ with hx'
  have hσ : (τ.σ (Transversal.qinv (H := H) (x * g)))⁻¹ = x' := by
    rw [hx, Transversal.qinv_σ_inv_mul, ← hx']
  have hab : τ.lam (x * g * h) = τ.lam (x * g) * τ.lam (x' * h) := by rw [τ.lam_mul (x * g) h, hσ]
  have habc : τ.lam (x * g * (h * j)) =
      τ.lam (x * g) * τ.lam (x' * h * j) := by
    rw [τ.lam_mul (x * g) (h * j), hσ, mul_assoc]
  have hbc : τ.lam (x' * h * j) =
      τ.lam (x' * h) * τ.lam ((τ.σ (Transversal.qinv (H := H) (x' * h)))⁻¹ * j) :=
    τ.lam_mul (x' * h) j
  have hgσ : A.ρ g * A.ρ (τ.σ (g⁻¹ • q)) = A.ρ (τ.σ q) * A.ρ ((τ.lam (x * g) : H) : G) := by
    rw [← map_mul, ← map_mul, hx]; exact congrArg _ (τ.mul_σ q g)
  rw [show x * (g * h) = x * g * h from (mul_assoc _ _ _).symm,
    show x * g * h * j = x * g * (h * j) from mul_assoc _ _ _,
    hab, habc, hbc, ← mul_apply_eq_comp, hgσ, mul_apply_eq_comp]
  simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left, ← map_add]
  congr 1
  have hu' := hu (τ.lam (x * g)) (τ.lam (x' * h))
    (τ.lam ((τ.σ (Transversal.qinv (H := H) (x' * h)))⁻¹ * j))
  exact hu'

lemma cor₂_add (u v : H × H → A) : cor₂ A τ (u + v) = cor₂ A τ u + cor₂ A τ v := by
  funext gh; obtain ⟨g₁, g₂⟩ := gh
  simp only [cor₂_apply, Pi.add_apply, map_add, Finset.sum_add_distrib]

lemma cor₂_smul (c : k) (u : H × H → A) : cor₂ A τ (c • u) = c • cor₂ A τ u := by
  funext gh; obtain ⟨g₁, g₂⟩ := gh
  simp only [cor₂_apply, Pi.smul_apply, map_smul, Finset.smul_sum]

omit [H.FiniteIndex] in
lemma res_mem_cocycles₂ {f : G × G → A} (hf : f ∈ cocycles₂ A) :
    (fun hh : H × H => f ((hh.1 : G), (hh.2 : G))) ∈ cocycles₂ (Rep.res H.subtype A) := by
  rw [mem_cocycles₂_iff] at hf ⊢
  intro a b c
  exact hf a b c

/-- **Corestriction of 2-cocycles.** For a subgroup `H` of finite index, a representation `A`
of `G` and a transversal `τ` of the left cosets of `H`, the `k`-linear map `u ↦ cor₂ u` from the
2-cocycles of the restriction of `A` to `H` to the 2-cocycles of `A`. -/
noncomputable def corCocycles₂ : cocycles₂ (Rep.res H.subtype A) →ₗ[k] cocycles₂ A where
  toFun u := ⟨cor₂ A τ u, cor₂_mem_cocycles₂ A τ u.2⟩
  map_add' u v := Subtype.ext (cor₂_add A τ u v)
  map_smul' c u := Subtype.ext (cor₂_smul A τ c u)

lemma coe_corCocycles₂ (u : cocycles₂ (Rep.res H.subtype A)) :
    (corCocycles₂ A τ u : G × G → A) = cor₂ A τ u := rfl

lemma H2π_corCocycles₂_eq_zero {u : cocycles₂ (Rep.res H.subtype A)}
    (hu : (u : H × H → A) ∈ coboundaries₂ (Rep.res H.subtype A)) :
    H2π A (corCocycles₂ A τ u) = 0 := by
  rw [H2π_eq_zero_iff]
  obtain ⟨v, hv⟩ := hu
  refine ⟨cor₁ A τ v, ?_⟩
  change (d₁₂ A).hom (cor₁ A τ v) = cor₂ A τ u
  rw [← cor₂_d₁₂, hv]

/-- **Corestriction on second cohomology.** For a subgroup `H` of finite index and a
representation `A` of `G`, the corestriction `H²(H, A) → H²(G, A)`, where `H²(H, A)` is the second
cohomology of the restriction of `A` to `H`, computed with a transversal `τ` of the left cosets of
`H`: the `k`-linear map that `cor₂` induces on second cohomology. It does not depend on `τ`
(`cores_eq_cores`). -/
noncomputable def cores : H2 (Rep.res H.subtype A) →ₗ[k] H2 A :=
  (H2π (Rep.res H.subtype A)).hom.liftOfSurjective
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)
    ⟨(H2π A).hom ∘ₗ corCocycles₂ A τ, fun x hx => by
      rw [LinearMap.mem_ker] at hx ⊢
      have hx' : (x : H × H → A) ∈ coboundaries₂ (Rep.res H.subtype A) :=
        (H2π_eq_zero_iff x).1 hx
      exact H2π_corCocycles₂_eq_zero A τ hx'⟩

/-- **Corestriction of the class of a 2-cocycle.** For a subgroup `H` of finite index, a
representation `A` of `G` and a transversal `τ` of the left cosets of `H`, the corestriction of
the class of a 2-cocycle `u` of `H` is the class of the 2-cocycle `cor₂ u` of `G`. -/
lemma cores_H2π (u : cocycles₂ (Rep.res H.subtype A)) :
    cores A τ (H2π _ u) = H2π A (corCocycles₂ A τ u) :=
  LinearMap.equivOfSurjective_apply _ _

/-! ### Independence of the transversal -/

/-- `cor₂`-type sums built from any map `η : G → H` in place of `τ.lam`. -/
private noncomputable def Phi (η : G → H) (u : H × H → A) : G × G → A := fun gg =>
  ∑ q : G ⧸ H, A.ρ (τ.σ q)
    (homog A u (η (τ.σ q)⁻¹) (η ((τ.σ q)⁻¹ * gg.1)) (η ((τ.σ q)⁻¹ * gg.1 * gg.2)))

private lemma Phi_apply (η : G → H) (u : H × H → A) (g₁ g₂ : G) : Phi A τ η u (g₁, g₂) =
    ∑ q : G ⧸ H, A.ρ (τ.σ q)
      (homog A u (η (τ.σ q)⁻¹) (η ((τ.σ q)⁻¹ * g₁)) (η ((τ.σ q)⁻¹ * g₁ * g₂))) := rfl

/-- The 1-cochain whose coboundary compares `Phi` for two maps `η η' : G → H`. -/
private noncomputable def bch (η η' : G → H) (u : H × H → A) : G → A := fun g =>
  ∑ q : G ⧸ H, A.ρ (τ.σ q) (W A η η' u (τ.σ q)⁻¹ ((τ.σ q)⁻¹ * g))

private lemma bch_apply (η η' : G → H) (u : H × H → A) (g : G) :
    bch A τ η η' u g = ∑ q : G ⧸ H, A.ρ (τ.σ q) (W A η η' u (τ.σ q)⁻¹ ((τ.σ q)⁻¹ * g)) := rfl

private theorem Phi_sub_Phi (η η' : G → H) (hη : ∀ (h : H) (y : G), η (h * y) = h * η y)
    (hη' : ∀ (h : H) (y : G), η' (h * y) = h * η' y)
    {u : H × H → A} (hu : u ∈ cocycles₂ (Rep.res H.subtype A)) :
    Phi A τ η' u - Phi A τ η u = (d₁₂ A).hom (bch A τ η η' u) := by
  funext gg
  obtain ⟨g₁, g₂⟩ := gg
  rw [Pi.sub_apply, d₁₂_hom_apply, Phi_apply, Phi_apply, bch_apply, bch_apply, bch_apply,
    map_sum]
  dsimp only
  have hre : ∑ q : G ⧸ H, A.ρ g₁ (A.ρ (τ.σ q) (W A η η' u (τ.σ q)⁻¹ ((τ.σ q)⁻¹ * g₂))) =
      ∑ q : G ⧸ H, A.ρ g₁ (A.ρ (τ.σ (g₁⁻¹ • q))
        (W A η η' u (τ.σ (g₁⁻¹ • q))⁻¹ ((τ.σ (g₁⁻¹ • q))⁻¹ * g₂))) :=
    (Fintype.sum_equiv (MulAction.toPerm g₁⁻¹) _ _ fun q => rfl).symm
  rw [hre, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  set x : G := (τ.σ q)⁻¹
  have hmul : g₁ * τ.σ (g₁⁻¹ • q) = τ.σ q * (τ.lam (x * g₁) : G) := τ.mul_σ q g₁
  have hinv : (τ.σ (g₁⁻¹ • q))⁻¹ = ((τ.lam (x * g₁))⁻¹ : H) * (x * g₁) := by
    have : τ.σ (g₁⁻¹ • q) = g₁⁻¹ * (τ.σ q * (τ.lam (x * g₁) : G)) := by
      rw [← hmul, inv_mul_cancel_left]
    rw [this, mul_inv_rev, mul_inv_rev, inv_inv, Subgroup.coe_inv, mul_assoc]
  have hρ : ∀ w : A, A.ρ (τ.σ q * (τ.lam (x * g₁) : G))
      (A.ρ (((τ.lam (x * g₁))⁻¹ : H) : G) w) = A.ρ (τ.σ q) w := fun w => by
    rw [← mul_apply_eq_comp, ← map_mul, mul_assoc, ← Subgroup.coe_mul, mul_inv_cancel,
      Subgroup.coe_one, mul_one]
  rw [← mul_apply_eq_comp, ← map_mul, hmul, hinv,
    mul_assoc (((τ.lam (x * g₁))⁻¹ : H) : G) (x * g₁) g₂, W_mul A η η' hη hη', hρ, ← map_sub,
    ← map_sub, ← map_add, W, W, W, mul_assoc x g₁ g₂]
  congr 1
  exact prism A (homog A u) (homog_cocycle A hu) η η' x (x * g₁) (x * (g₁ * g₂))

private theorem cor₂_eq_Phi (u : H × H → A) : cor₂ A τ u = Phi A τ τ.lam u := by
  funext gg
  obtain ⟨g₁, g₂⟩ := gg
  rw [cor₂_apply, Phi_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Transversal.lam_σ_inv, homog_one]

private theorem cor₂_eq_Phi' (τ' : Transversal H) (u : H × H → A) :
    cor₂ A τ' u = Phi A τ τ'.lam u := by
  funext gg
  obtain ⟨g₁, g₂⟩ := gg
  rw [cor₂_apply, Phi_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hq : Transversal.qinv (H := H) (τ.σ q)⁻¹ = q := τ.qinv_σ_inv q
  have hκ : (τ.σ q : G) * (τ'.lam (τ.σ q)⁻¹ : G) = τ'.σ q := by
    rw [τ'.coe_lam, hq, mul_inv_cancel_left]
  have hF : ∀ g : G,
      τ'.lam ((τ.σ q)⁻¹ * g) = τ'.lam (τ.σ q)⁻¹ * τ'.lam ((τ'.σ q)⁻¹ * g) := fun g => by
    rw [τ'.lam_mul, hq]
  rw [homog, ← mul_apply_eq_comp, ← map_mul, hκ, mul_assoc ((τ.σ q)⁻¹) g₁ g₂, hF g₁,
    hF (g₁ * g₂), inv_mul_cancel_left, mul_inv_rev,
    mul_assoc ((τ'.lam ((τ'.σ q)⁻¹ * g₁))⁻¹), inv_mul_cancel_left, mul_assoc ((τ'.σ q)⁻¹) g₁ g₂]

/-- **Corestriction does not depend on the transversal.** For a subgroup `H` of finite index, a
representation `A` of `G` and two transversals `τ`, `τ'` of the left cosets of `H`, the
corestrictions `H²(H, A) → H²(G, A)` computed with `τ` and with `τ'` agree on every class. -/
theorem cores_eq_cores (τ' : Transversal H) (x : H2 (Rep.res H.subtype A)) :
    cores A τ x = cores A τ' x := by
  induction x using H2_induction_on with
  | h u =>
    have hu : (⇑u : H × H → A) ∈ cocycles₂ (Rep.res H.subtype A) := u.2
    rw [cores_H2π, cores_H2π, H2π_eq_iff, coe_corCocycles₂, coe_corCocycles₂, cor₂_eq_Phi,
      cor₂_eq_Phi' A τ τ']
    refine ⟨-bch A τ τ.lam τ'.lam u, ?_⟩
    rw [map_neg, ← Phi_sub_Phi A τ τ.lam τ'.lam (Transversal.lam_mul_left τ)
      (Transversal.lam_mul_left τ') hu, neg_sub]

end Cor
end Cores
end groupCohomology

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_GroupCohomology_Corestriction2.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Corestriction in degree two

For a finite-index subgroup `H ≤ G`, a transversal gives explicit
corestriction maps on 1- and 2-cochains. They preserve cocycles and
coboundaries, hence induce corestriction `cores : H²(H, A) → H²(G, A)`.
-/

@[expose] public section

open CategoryTheory groupCohomology

namespace groupCohomology

universe u
namespace Cores

section Transversal
variable {G : Type*} [Group G] (H : Subgroup G)

structure Transversal where
  σ : G ⧸ H → G
  mk_σ : ∀ q, (σ q : G ⧸ H) = q
  σ_one : σ ((1 : G) : G ⧸ H) = 1

namespace Transversal
variable {H}

lemma nonempty : Nonempty (Transversal H) := by
  classical
  refine ⟨⟨Function.update Quotient.out ((1 : G) : G ⧸ H) 1, fun q => ?_,
    Function.update_self _ _ _⟩⟩
  by_cases hq : q = ((1 : G) : G ⧸ H)
  · subst hq; rw [Function.update_self]
  · rw [Function.update_of_ne hq]; exact q.out_eq

variable (τ : Transversal H)

abbrev qinv (x : G) : G ⧸ H := ((x⁻¹ : G) : G ⧸ H)

lemma lam_mem (x : G) : x * τ.σ (qinv (H := H) x) ∈ H := by
  have h : ((τ.σ (qinv (H := H) x) : G) : G ⧸ H) = ((x⁻¹ : G) : G ⧸ H) := τ.mk_σ _
  rw [QuotientGroup.eq] at h
  have := H.inv_mem h
  rwa [mul_inv_rev, inv_inv, inv_inv] at this

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

end Transversal
end Transversal

section Cor
variable {k G : Type u} [CommRing k] [Group G] {H : Subgroup G} [H.FiniteIndex]
  (A : Rep k G) (τ : Transversal H)

@[reducible, local instance] noncomputable def fintypeQuot : Fintype (G ⧸ H) := Fintype.ofFinite _

noncomputable def cor₁ (u : H → A) : G → A := fun g =>
  ∑ q : G ⧸ H, A.ρ (τ.σ q) (u (τ.lam ((τ.σ q)⁻¹ * g)))

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
    ← Module.End.mul_apply, hgσ, Module.End.mul_apply, ← map_sub, ← map_add]
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
    hab, habc, hbc, ← Module.End.mul_apply, hgσ, Module.End.mul_apply]
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

noncomputable def cores : H2 (Rep.res H.subtype A) →ₗ[k] H2 A :=
  (H2π (Rep.res H.subtype A)).hom.liftOfSurjective
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)
    ⟨(H2π A).hom ∘ₗ corCocycles₂ A τ, fun x hx => by
      rw [LinearMap.mem_ker] at hx ⊢
      have hx' : (x : H × H → A) ∈ coboundaries₂ (Rep.res H.subtype A) :=
        (H2π_eq_zero_iff x).1 hx
      exact H2π_corCocycles₂_eq_zero A τ hx'⟩

lemma cores_H2π (u : cocycles₂ (Rep.res H.subtype A)) :
    cores A τ (H2π _ u) = H2π A (corCocycles₂ A τ u) :=
  LinearMap.equivOfSurjective_apply _ _

end Cor
end Cores
end groupCohomology

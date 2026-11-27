/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from `ZInQKernel/Contrib/OneProof/BdRInvariants.lean`,
`ZInQKernel/Contrib/OneProof/LogPTranscendenceBdR.lean` and
`ZInQKernel/Contrib/OneProof/DeRhamPrint.lean` (https://github.com/Deicyde/diophantine-z-q),
compared with the source files at commit `e9956cda4174c060ff85f5a6ddc7e4003e63fdd3`.
Copyright 2026 the contributors to Deicyde/diophantine-z-q.
Licensed under the Apache License, Version 2.0.
-/

module

public import MathlibExt.RingTheory.Perfectoid.DeRhamPeriodRingAlgebraic
public import MathlibExt.RingTheory.Perfectoid.DeRhamPeriodRingUniformizer

/-!
# The Galois invariants of `B_dR`

Let `K` be a finite extension of `ℚ_p` inside `ℚ̄_p = PadicAlgCl p`. We prove
`B_dR ^ Gal(ℚ̄_p/K) = K` (`PadicComplexInt.fixedPoints_bDeRham_eq_range`), where `K` is embedded
in `B_dR = BDeRham 𝓞_ℂ_[p] p` through `ℚ̄_p ⊆ B_dR^+ ⊆ B_dR`
(`PadicComplexInt.padicAlgClToBDeRhamPlus`), and `σ ∈ Gal(ℚ̄_p/K)` acts by
`PadicComplexInt.galoisBDeRham p σ`. This is the statement `(B_dR)^{G_K} = K` of J.-M. Fontaine,
*Le corps des périodes p-adiques*, Astérisque 223 (1994), Exposé II, §1.5.7 p. 74 (there for
every open subgroup of `Gal(ℚ̄_p/ℚ_p)`, deduced from Tate's theorems), for `K` finite over `ℚ_p`;
for `K = ℚ_p` it reads `(B_dR)^{G_{ℚ_p}} = ℚ_p`, whose inclusion `⊆` is
`PadicComplexInt.exists_eq_algebraMap_of_forall_galoisBDeRham_eq_self`.

## Proof

Write `T = [ε] - 1`, a uniformizer of `B_dR^+` with `σ(T) = T · w_σ` and `θ(w_σ) = χ(σ)`
(`PadicComplexInt.exists_galoisBDeRhamPlus_algebraMap_teichmuller_epsilon_sub_one`). A nonzero
invariant `x = T^{j-k} u` (`u` a unit of `B_dR^+`) gives `χ(σ)^{j-k} σ(θ u) = θ u` for every
`σ ∈ Gal(ℚ̄_p/K)`, so `j = k` by Tate's theorem on the twists of `ℂ_p`
(`PadicComplex.fixedPoints_twist_eq_singleton_zero`): `x` is a unit of `B_dR^+`. Then
`θ(x) ∈ ℂ_p^{Gal(ℚ̄_p/K)} = K` by the Ax–Sen–Tate theorem (`PadicComplex.fixedPoints_eq_range`),
and `x` minus the image of `θ(x) ∈ K` is an invariant in the kernel of `θ`, hence `0`.
-/

@[expose] public noncomputable section

open Ideal WittVector MathlibExt.AlgebraicGeometry.HodgeTateComparison

namespace PadicComplexInt

variable (p : ℕ) [hp : Fact p.Prime]

local notation "𝔹⁺" => BDeRhamPlus 𝓞_ℂ_[p] p
local notation "𝔹" => BDeRham 𝓞_ℂ_[p] p

/-- For a uniformizer `π` of `B_dR^+`, every nonzero `x ∈ B_dR` satisfies `x · π ^ k = u · π ^ j`
for some `j k : ℕ` and some unit `u` of `B_dR^+`. -/
private theorem exists_mul_pow_eq_unit_mul_pow {π : 𝔹⁺} (hπ : Irreducible π) {x : 𝔹}
    (hx0 : x ≠ 0) :
    ∃ (j k : ℕ) (u : 𝔹⁺ˣ),
      x * algebraMap 𝔹⁺ 𝔹 π ^ k = algebraMap 𝔹⁺ 𝔹 u * algebraMap 𝔹⁺ 𝔹 π ^ j := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective 𝔹⁺ x
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hx0 (by rw [map_zero, zero_div])
  obtain ⟨j, ua, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hπ
  obtain ⟨k, ub, rfl⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hb) hπ
  have hπ0 : algebraMap 𝔹⁺ 𝔹 π ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap_bDeRham_injective p)).mpr hπ.ne_zero
  refine ⟨j, k, ua * ub⁻¹, ?_⟩
  simp only [Units.val_mul, map_mul, map_units_inv, map_pow]
  field_simp

open PadicComplex in
/-- Let `u` be a unit of `B_dR^+` with `θ(u) · χ(σ) ^ k = σ(θ(u)) · χ(σ) ^ j` for every
`σ ∈ Gal(ℚ̄_p/K)`, where `χ` is the cyclotomic character. Then `j = k`, by Tate's theorem on the
twists of `ℂ_p`. -/
private theorem eq_of_forall_fontaineThetaBDeRhamPlus_mul_pow_eq
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] (u : 𝔹⁺ˣ)
    {j k : ℕ}
    (h : ∀ σ ∈ K.fixingSubgroup, fontaineThetaBDeRhamPlus p u *
        algebraMap ℚ_[p] ℂ_[p] (cyclotomicScalar p σ) ^ k =
      completionGalois p σ (fontaineThetaBDeRhamPlus p u) *
        algebraMap ℚ_[p] ℂ_[p] (cyclotomicScalar p σ) ^ j) :
    j = k := by
  by_contra hjk
  refine (u.isUnit.map (fontaineThetaBDeRhamPlus p)).ne_zero ?_
  refine eq_zero_of_forall_mem_fixingSubgroup_cyclotomicScalar_zpow_smul_completionGalois_eq_self
    p K (i := (j : ℤ) - k) (by omega) fun σ hσ => ?_
  have hc : algebraMap ℚ_[p] ℂ_[p] (cyclotomicScalar p σ) ≠ 0 :=
    (map_ne_zero _).mpr (cyclotomicScalar_ne_zero p σ)
  rw [Algebra.smul_def, map_zpow₀, zpow_sub₀ hc, zpow_natCast, zpow_natCast, div_mul_eq_mul_div,
    div_eq_iff (pow_ne_zero k hc)]
  linear_combination (h σ hσ).symm

/-- A nonzero element of `B_dR` fixed by `Gal(ℚ̄_p/K)`, for `K` finite over `ℚ_p` inside `ℚ̄_p`, is
the image of a unit of `B_dR^+`. -/
theorem exists_unit_of_forall_galoisBDeRham_eq_self (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] {x : 𝔹} (hx0 : x ≠ 0)
    (hx : ∀ σ ∈ K.fixingSubgroup, galoisBDeRham p σ x = x) :
    ∃ u : 𝔹⁺ˣ, x = algebraMap 𝔹⁺ 𝔹 u := by
  have hT := irreducible_algebraMap_teichmuller_epsilon_sub_one p
  have hT0 := (map_ne_zero_iff _ (algebraMap_bDeRham_injective p)).mpr hT.ne_zero
  obtain ⟨j, k, u, hxu⟩ := exists_mul_pow_eq_unit_mul_pow p hT hx0
  have hjk : j = k := by
    refine eq_of_forall_fontaineThetaBDeRhamPlus_mul_pow_eq p K u fun σ hσ => ?_
    obtain ⟨w, hw, hθw⟩ := exists_galoisBDeRhamPlus_algebraMap_teichmuller_epsilon_sub_one p σ
    have h2 := congrArg (galoisBDeRham p σ) hxu
    simp only [map_mul, map_pow, hx σ hσ, galoisBDeRham_algebraMap, hw] at h2
    have h3 : algebraMap 𝔹⁺ 𝔹 (u * w ^ k) =
        algebraMap 𝔹⁺ 𝔹 (galoisBDeRhamPlus p σ u * w ^ j) := by
      simp only [map_mul, map_pow]
      apply mul_left_cancel₀ (pow_ne_zero j hT0)
      linear_combination h2 - algebraMap 𝔹⁺ 𝔹 w ^ k * hxu
    have h4 := congrArg (fontaineThetaBDeRhamPlus p) (algebraMap_bDeRham_injective p h3)
    simpa only [map_mul, map_pow, fontaineThetaBDeRhamPlus_galoisBDeRhamPlus, hθw] using h4
  subst hjk
  exact ⟨u, mul_right_cancel₀ (pow_ne_zero _ hT0) hxu⟩

/-- An element of the kernel of `θ : B_dR^+ → ℂ_[p]` fixed by `Gal(ℚ̄_p/K)` is `0`. -/
private theorem eq_zero_of_fontaineThetaBDeRhamPlus_eq_zero
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] {v : 𝔹⁺}
    (hv : fontaineThetaBDeRhamPlus p v = 0)
    (hfix : ∀ σ ∈ K.fixingSubgroup, galoisBDeRhamPlus p σ v = v) : v = 0 := by
  by_contra hv0
  obtain ⟨u, hu⟩ := exists_unit_of_forall_galoisBDeRham_eq_self p K
    ((map_ne_zero_iff _ (algebraMap_bDeRham_injective p)).mpr hv0) fun σ hσ => by
      rw [galoisBDeRham_algebraMap, hfix σ hσ]
  rw [algebraMap_bDeRham_injective p hu] at hv
  exact (u.isUnit.map (fontaineThetaBDeRhamPlus p)).ne_zero hv

/-- **`B_dR ^ Gal(ℚ̄_p/K) = K`**: for `K` finite over `ℚ_p` inside `ℚ̄_p`, the elements of `B_dR`
fixed by every `σ ∈ Gal(ℚ̄_p/K)` are exactly the images of the elements of `K` under
`ℚ̄_p ⊆ B_dR^+ ⊆ B_dR`. -/
theorem fixedPoints_bDeRham_eq_range (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] :
    {x : 𝔹 | ∀ σ ∈ K.fixingSubgroup, galoisBDeRham p σ x = x} =
      Set.range fun y : K => algebraMap 𝔹⁺ 𝔹 (padicAlgClToBDeRhamPlus p y) := by
  have hι (σ) (hσ : σ ∈ K.fixingSubgroup) (y : K) :
      galoisBDeRhamPlus p σ (padicAlgClToBDeRhamPlus p y) = padicAlgClToBDeRhamPlus p y := by
    rw [galoisBDeRhamPlus_padicAlgClToBDeRhamPlus,
      (IntermediateField.mem_fixingSubgroup_iff K σ).mp hσ y y.2]
  ext x
  refine ⟨fun hx => ?_, ?_⟩
  · by_cases hx0 : x = 0
    · exact ⟨0, by simp [hx0]⟩
    obtain ⟨u, rfl⟩ := exists_unit_of_forall_galoisBDeRham_eq_self p K hx0 hx
    have hu (σ) (hσ : σ ∈ K.fixingSubgroup) : galoisBDeRhamPlus p σ u = u :=
      algebraMap_bDeRham_injective p (by rw [← galoisBDeRham_algebraMap, hx σ hσ])
    obtain ⟨y, hy⟩ := (PadicComplex.forall_completionGalois_eq_self_iff_mem_range p K
      (fontaineThetaBDeRhamPlus p u)).mp fun σ hσ => by
        rw [← fontaineThetaBDeRhamPlus_galoisBDeRhamPlus, hu σ hσ]
    have hy' : ((y : PadicAlgCl p) : ℂ_[p]) = fontaineThetaBDeRhamPlus p u := hy
    refine ⟨y, congrArg (algebraMap 𝔹⁺ 𝔹) (sub_eq_zero.mp ?_).symm⟩
    refine eq_zero_of_fontaineThetaBDeRhamPlus_eq_zero p K ?_ fun σ hσ => ?_
    · rw [map_sub, fontaineThetaBDeRhamPlus_padicAlgClToBDeRhamPlus, hy', sub_self]
    · rw [map_sub, hu σ hσ, hι σ hσ y]
  · rintro ⟨y, rfl⟩ σ hσ
    rw [galoisBDeRham_algebraMap, hι σ hσ y]

/-- **`B_dR ^ Gal(ℚ̄_p/ℚ_p) ⊆ ℚ_p`**: an element of `B_dR` fixed by every `σ ∈ Gal(ℚ̄_p/ℚ_p)` is the
image of an element of `ℚ_[p]`. -/
theorem exists_eq_algebraMap_of_forall_galoisBDeRham_eq_self {x : 𝔹}
    (hx : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, galoisBDeRham p σ x = x) :
    ∃ c : ℚ_[p], x = algebraMap ℚ_[p] 𝔹 c := by
  obtain ⟨⟨y, hy⟩, rfl⟩ := (fixedPoints_bDeRham_eq_range p ⊥).subset
    (show x ∈ {x : 𝔹 | ∀ σ ∈ (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p)).fixingSubgroup,
      galoisBDeRham p σ x = x} from fun σ _ => hx σ)
  obtain ⟨c, rfl⟩ := IntermediateField.mem_bot.mp hy
  refine ⟨c, ?_⟩
  change algebraMap 𝔹⁺ 𝔹 (padicAlgClToBDeRhamPlus p (algebraMap ℚ_[p] _ c)) = _
  rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

end PadicComplexInt

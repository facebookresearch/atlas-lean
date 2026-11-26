/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The exact-source consumer reproduces the theorem type from
`Theorems/Thm_Module_free_of_torsionBySet_eq_annihilator_smul.lean`
in https://github.com/anthropics/fermats-last-theorem at commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright (c) 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0.
The upstream NOTICE also credits Mathlib and its respective authors under Apache 2.0.
-/

module

public import MathlibExt.RingTheory.LocalRing.FreeOfBalancedPairing
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.AdjoinRoot

universe u w x

/-- The original statement, with its original binders, follows from the
public theorem. -/
example
    {𝒪 : Type u} {T : Type w} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    [CommRing T] [IsLocalRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
    (πT : T →ₐ[𝒪] 𝒪) (hη : (RingHom.ker πT).annihilator.map πT ≠ ⊥)
    (C : T →ₗ[𝒪] T →ₗ[𝒪] 𝒪) (hC : ∀ s t u : T, C (s * t) u = C t (s * u))
    (hCb : Function.Bijective C)
    (M : Type x) [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    [Module.Finite 𝒪 M] [Module.Free 𝒪 M]
    (B : M →ₗ[𝒪] M →ₗ[𝒪] 𝒪) (hB : ∀ (t : T) (m n : M), B (t • m) n = B m (t • n))
    (hBb : Function.Bijective B)
    (hrank : Module.finrank 𝒪 M =
      Module.finrank 𝒪 (Submodule.torsionBySet T M ↑(RingHom.ker πT)) * Module.finrank 𝒪 T)
    (hsat : Submodule.torsionBySet T M ↑(RingHom.ker πT) = (RingHom.ker πT).annihilator • ⊤) :
    Module.Free T M :=
  Module.free_of_torsionBySet_eq_annihilator_smul πT hη C hC hCb M B hB hBb hrank hsat

/-- Higher-universe consumer: all three types in `Type 1`. -/
example
    {𝒪 : Type 1} {T : Type 1} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    [CommRing T] [IsLocalRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
    (πT : T →ₐ[𝒪] 𝒪) (hη : (RingHom.ker πT).annihilator.map πT ≠ ⊥)
    (C : T →ₗ[𝒪] T →ₗ[𝒪] 𝒪) (hC : ∀ s t u : T, C (s * t) u = C t (s * u))
    (hCb : Function.Bijective C)
    (M : Type 1) [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    [Module.Finite 𝒪 M] [Module.Free 𝒪 M]
    (B : M →ₗ[𝒪] M →ₗ[𝒪] 𝒪) (hB : ∀ (t : T) (m n : M), B (t • m) n = B m (t • n))
    (hBb : Function.Bijective B)
    (hrank : Module.finrank 𝒪 M =
      Module.finrank 𝒪 (Submodule.torsionBySet T M ↑(RingHom.ker πT)) * Module.finrank 𝒪 T)
    (hsat : Submodule.torsionBySet T M ↑(RingHom.ker πT) = (RingHom.ker πT).annihilator • ⊤) :
    Module.Free T M :=
  Module.free_of_torsionBySet_eq_annihilator_smul πT hη C hC hCb M B hB hBb hrank hsat

namespace FreeOfBalancedPairingTest

/-! ### The field case -/

/-- Over `ℚ`, the identity augmentation has kernel `⊥`. -/
private theorem ker_algHom_id_rat : RingHom.ker (AlgHom.id ℚ ℚ) = ⊥ :=
  (RingHom.injective_iff_ker_eq_bot _).mp Function.injective_id

/-- Multiplication is a perfect pairing on `ℚ`. -/
private theorem bijective_mul_rat : Function.Bijective (LinearMap.mul ℚ ℚ) :=
  ⟨fun a b h => by simpa using LinearMap.congr_fun h 1,
    fun f => ⟨f 1, LinearMap.ext_ring (by simp)⟩⟩

/-- Every element of `ℚ` is killed by the kernel `⊥` of the identity augmentation. -/
private theorem torsionBySet_ker_algHom_id_rat :
    Submodule.torsionBySet ℚ ℚ ↑(RingHom.ker (AlgHom.id ℚ ℚ)) = ⊤ := by
  rw [ker_algHom_id_rat]
  ext m
  simp

/-- The hypotheses hold together: `𝒪 = T = M = ℚ`, with the identity augmentation and
multiplication as both pairings, satisfies every one of them. -/
example : Module.Free ℚ ℚ :=
  Module.free_of_torsionBySet_eq_annihilator_smul (AlgHom.id ℚ ℚ)
    (by rw [ker_algHom_id_rat, Submodule.annihilator_bot, Ideal.map_top]; exact top_ne_bot)
    (LinearMap.mul ℚ ℚ) (fun s t u => by simp only [LinearMap.mul_apply']; ring)
    bijective_mul_rat ℚ (LinearMap.mul ℚ ℚ)
    (fun t m n => by simp only [smul_eq_mul, LinearMap.mul_apply']; ring) bijective_mul_rat
    (by rw [torsionBySet_ker_algHom_id_rat, finrank_top, Module.finrank_self, one_mul])
    (by rw [torsionBySet_ker_algHom_id_rat, ker_algHom_id_rat, Submodule.annihilator_bot,
      Submodule.top_smul])

/-! ### A local algebra of rank two

Over a field the hypotheses force `T = 𝒪`, so the field case is degenerate. Here `𝒪` is a
local principal ideal domain with a nonzero `ϖ` in its maximal ideal, `T = 𝒪[X] ⧸ (X ^ 2 - ϖ X)`
with augmentation `X ↦ 0`, `M = T`, and both pairings send `(s, t)` to the `X`-coefficient of
`s t` in the basis `1, X`. -/

section RankTwo

open Polynomial

variable {𝒪 : Type*} [CommRing 𝒪] (ϖ : 𝒪)

/-- `X ^ 2 - ϖ X`. -/
private noncomputable abbrev g : 𝒪[X] := X ^ 2 - C ϖ * X

local notation "T" => AdjoinRoot (g ϖ)
local notation "r" => AdjoinRoot.root (g ϖ)
local notation "ι" => algebraMap 𝒪 (AdjoinRoot (g ϖ))

private theorem root_sq : r ^ 2 = ι ϖ * r := by
  have h := AdjoinRoot.eval₂_root (g ϖ)
  simp only [g, eval₂_sub, eval₂_X_pow, eval₂_mul, eval₂_C, eval₂_X] at h
  rw [← sub_eq_zero, ← h]
  rfl

private theorem mul_coords (α β α' β' : 𝒪) :
    (ι α + ι β * r) * (ι α' + ι β' * r) = ι (α * α') + ι (α * β' + α' * β + ϖ * β * β') * r := by
  simp only [map_add, map_mul]
  linear_combination (ι β * ι β') * root_sq ϖ

private theorem mul_root (α β : 𝒪) : (ι α + ι β * r) * r = ι 0 + ι (α + ϖ * β) * r := by
  simp only [map_add, map_mul, map_zero, zero_add]
  linear_combination ι β * root_sq ϖ

/-- The augmentation `X ↦ 0`. -/
private noncomputable def πT : T →ₐ[𝒪] 𝒪 :=
  AdjoinRoot.liftAlgHom (g ϖ) (AlgHom.id 𝒪 𝒪) 0 (by simp [g])

private theorem πT_coords (α β : 𝒪) : πT ϖ (ι α + ι β * r) = α := by
  simp [πT, AdjoinRoot.liftAlgHom_root]

private theorem root_mem_ker : r ∈ RingHom.ker (πT ϖ) := by
  rw [RingHom.mem_ker, ← zero_add r, ← map_zero ι, ← one_mul r, ← map_one ι, πT_coords]

private theorem g_monic : (g ϖ).Monic :=
  monic_X_pow_sub (lt_of_le_of_lt (degree_C_mul_X_le ϖ) (by exact_mod_cast one_lt_two))

section Basis

variable [Nontrivial 𝒪]

private theorem g_natDegree : (g ϖ).natDegree = 2 := by
  rw [g, natDegree_sub_eq_left_of_natDegree_lt] <;> simp only [natDegree_X_pow]
  exact lt_of_le_of_lt ((natDegree_C_mul_le ϖ X).trans natDegree_X_le) one_lt_two

/-- The basis `1, X` of `T`. -/
private noncomputable def b : Module.Basis (Fin 2) 𝒪 T :=
  (AdjoinRoot.powerBasis' (g_monic ϖ)).basis.reindex (finCongr (g_natDegree ϖ))

private theorem b_zero : b ϖ 0 = 1 := by
  rw [b, Module.Basis.reindex_apply, PowerBasis.coe_basis]
  exact pow_zero _

private theorem b_one : b ϖ 1 = r := by
  rw [b, Module.Basis.reindex_apply, PowerBasis.coe_basis]
  exact pow_one _

/-- `T` has rank two over `𝒪`, so `T ≠ 𝒪`. -/
example : Module.finrank 𝒪 T = 2 := by
  rw [Module.finrank_eq_card_basis (b ϖ), Fintype.card_fin]

private theorem exists_coords (t : T) : ∃ α β : 𝒪, t = ι α + ι β * r := by
  refine ⟨(b ϖ).repr t 0, (b ϖ).repr t 1, ?_⟩
  conv_lhs => rw [← (b ϖ).sum_repr t]
  rw [Fin.sum_univ_two, b_zero, b_one, Algebra.smul_def, Algebra.smul_def, mul_one]

private theorem coords_eq_zero {α β : 𝒪} (h : ι α + ι β * r = 0) : α = 0 ∧ β = 0 := by
  have := Fintype.linearIndependent_iff.mp (b ϖ).linearIndependent ![α, β]
  simp only [Fin.sum_univ_two, b_zero, b_one, Matrix.cons_val_zero, Matrix.cons_val_one,
    Algebra.smul_def, mul_one] at this
  exact ⟨this h 0, this h 1⟩

private theorem coord_one_coords (α β : 𝒪) : (b ϖ).coord 1 (ι α + ι β * r) = β := by
  rw [← mul_one (ι α), ← Algebra.smul_def, ← Algebra.smul_def, ← b_zero, ← b_one, map_add,
    map_smul, map_smul, Module.Basis.coord_apply, Module.Basis.coord_apply,
    Module.Basis.repr_self, Module.Basis.repr_self]
  simp

private theorem mem_ker_πT {t : T} (ht : t ∈ RingHom.ker (πT ϖ)) :
    ∃ β : 𝒪, t = ι 0 + ι β * r := by
  obtain ⟨α, β, rfl⟩ := exists_coords ϖ t
  have hα : α = 0 := by rw [RingHom.mem_ker, πT_coords] at ht; exact ht
  exact ⟨β, by rw [hα]⟩

/-- `X - ϖ` kills the kernel `(X)` of the augmentation. -/
private theorem x₀_mem : ι (-ϖ) + ι 1 * r ∈ (RingHom.ker (πT ϖ)).annihilator := by
  rw [Submodule.mem_annihilator]
  intro k hk
  obtain ⟨β, rfl⟩ := mem_ker_πT ϖ hk
  rw [smul_eq_mul, mul_coords]
  simp

/-- The congruence ideal contains `πT (X - ϖ) = -ϖ ≠ 0`. -/
private theorem congruenceIdeal_ne_bot {ϖ : 𝒪} (hϖ0 : ϖ ≠ 0) :
    (RingHom.ker (πT ϖ)).annihilator.map (πT ϖ) ≠ ⊥ := by
  intro h
  have hmem := Ideal.mem_map_of_mem (πT ϖ) (x₀_mem ϖ)
  rw [h, Ideal.mem_bot, πT_coords] at hmem
  exact hϖ0 (neg_eq_zero.mp hmem)

/-- The pairing sending `(s, t)` to the `X`-coefficient of `s t`. -/
private noncomputable def pairing : T →ₗ[𝒪] T →ₗ[𝒪] 𝒪 :=
  (LinearMap.mul 𝒪 T).compr₂ ((b ϖ).coord 1)

private theorem pairing_apply (s t : T) : pairing ϖ s t = (b ϖ).coord 1 (s * t) := rfl

private theorem pairing_balanced (s t u : T) : pairing ϖ (s * t) u = pairing ϖ t (s * u) := by
  rw [pairing_apply, pairing_apply, mul_assoc, mul_left_comm]

/-- The pairing is perfect: its Gram matrix in the basis `1, X` is `!![0, 1; 1, ϖ]`. -/
private theorem bijective_pairing : Function.Bijective (pairing ϖ) := by
  refine ⟨(injective_iff_map_eq_zero (pairing ϖ)).mpr fun t ht => ?_, fun f => ?_⟩
  · obtain ⟨α, β, rfl⟩ := exists_coords ϖ t
    have h1 := LinearMap.congr_fun ht 1
    have h2 := LinearMap.congr_fun ht r
    rw [pairing_apply, mul_one, coord_one_coords, LinearMap.zero_apply] at h1
    rw [pairing_apply, mul_root, coord_one_coords, LinearMap.zero_apply, h1, mul_zero,
      add_zero] at h2
    rw [h1, h2, map_zero, zero_mul, add_zero]
  · refine ⟨ι (f r - ϖ * f 1) + ι (f 1) * r, (b ϖ).ext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)⟩
    · rw [b_zero, pairing_apply, mul_one, coord_one_coords]
    · rw [b_one, pairing_apply, mul_root, coord_one_coords]
      ring

private theorem exists_smul_of_mul_root_eq_zero {t : T} (ht : t * r = 0) :
    ∃ c : 𝒪, t = c • (ι (-ϖ) + ι 1 * r) := by
  obtain ⟨α, β, rfl⟩ := exists_coords ϖ t
  rw [mul_root] at ht
  have hα : ι α + ι ϖ * ι β = 0 := by
    rw [← map_mul, ← map_add, (coords_eq_zero ϖ ht).2, map_zero]
  refine ⟨β, ?_⟩
  rw [Algebra.smul_def, map_neg, map_one, one_mul]
  linear_combination hα

private theorem x₀_mem_torsion :
    ι (-ϖ) + ι 1 * r ∈ Submodule.torsionBySet T T ↑(RingHom.ker (πT ϖ)) :=
  (Submodule.mem_torsionBySet_iff _ _).mpr fun ⟨a, ha⟩ => by
    rw [smul_eq_mul, mul_comm]
    exact Submodule.mem_annihilator.mp (x₀_mem ϖ) a ha

/-- The `ker πT`-torsion of `T` is the line `𝒪 (X - ϖ)`. -/
private theorem finrank_torsion :
    Module.finrank 𝒪 (Submodule.torsionBySet T T ↑(RingHom.ker (πT ϖ))) = 1 := by
  let x₀ : Submodule.torsionBySet T T ↑(RingHom.ker (πT ϖ)) := ⟨_, x₀_mem_torsion ϖ⟩
  have hinj : Function.Injective (LinearMap.toSpanSingleton 𝒪 _ x₀) := by
    refine (injective_iff_map_eq_zero _).mpr fun c hc => ?_
    have h : c • (ι (-ϖ) + ι 1 * r) = 0 := congrArg Subtype.val hc
    rw [Algebra.smul_def, mul_add, ← map_mul, ← mul_assoc, ← map_mul, mul_one] at h
    exact (coords_eq_zero ϖ h).2
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton 𝒪 _ x₀) := by
    rintro ⟨t, ht⟩
    have htr : t * r = 0 := by
      rw [mul_comm, ← smul_eq_mul]
      exact (Submodule.mem_torsionBySet_iff _ _).mp ht ⟨r, root_mem_ker ϖ⟩
    obtain ⟨c, rfl⟩ := exists_smul_of_mul_root_eq_zero ϖ htr
    exact ⟨c, rfl⟩
  rw [← (LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩).finrank_eq, Module.finrank_self]

end Basis

/-- For `M = T`, the torsion submodule by an ideal is its annihilator. -/
private theorem torsionBySet_self_eq {R : Type*} [CommRing R] (I : Ideal R) :
    Submodule.torsionBySet R R ↑I = I.annihilator • ⊤ := by
  ext m
  simp [Submodule.mem_torsionBySet_iff, Submodule.mem_annihilator, mul_comm]

variable [IsLocalRing 𝒪] {ϖ}

private theorem isUnit_coords (hϖ : ϖ ∈ IsLocalRing.maximalIdeal 𝒪) {α : 𝒪} (hα : IsUnit α)
    (β : 𝒪) : IsUnit (ι α + ι β * r) := by
  have hv : IsUnit (α + ϖ * β) := by
    by_contra h
    have h1 : α + ϖ * β ∈ IsLocalRing.maximalIdeal 𝒪 := (IsLocalRing.mem_maximalIdeal _).mpr h
    have h2 : α ∈ IsLocalRing.maximalIdeal 𝒪 := by
      simpa using Ideal.sub_mem _ h1 (Ideal.mul_mem_right β _ hϖ)
    exact h2 hα
  obtain ⟨u, rfl⟩ := hα
  obtain ⟨v, hv⟩ := hv
  refine IsUnit.of_mul_eq_one (ι ↑u⁻¹ + ι (-(↑u⁻¹ * β * ↑v⁻¹)) * r) ?_
  have h1 : (↑u : 𝒪) * ↑u⁻¹ = 1 := u.mul_inv
  have h2 : (↑u : 𝒪) * -(↑u⁻¹ * β * ↑v⁻¹) + ↑u⁻¹ * β + ϖ * β * -(↑u⁻¹ * β * ↑v⁻¹) = 0 := by
    linear_combination (↑u⁻¹ * β * ↑v⁻¹) * hv - (↑u⁻¹ * β) * v.mul_inv
  rw [mul_coords, h1, h2, map_one, map_zero, zero_mul, add_zero]

/-- `T` is local: an element is a unit as soon as its augmentation is. -/
private theorem isLocalRing (hϖ : ϖ ∈ IsLocalRing.maximalIdeal 𝒪) : IsLocalRing T := by
  have : IsLocalHom (πT ϖ : T →+* 𝒪) := by
    refine ⟨fun t ht => ?_⟩
    obtain ⟨α, β, rfl⟩ := exists_coords ϖ t
    have h : (πT ϖ : T →+* 𝒪) (ι α + ι β * r) = α := πT_coords ϖ α β
    rw [h] at ht
    exact isUnit_coords hϖ ht β
  exact (πT ϖ : T →+* 𝒪).domain_isLocalRing

/-- The hypotheses hold together with `T` of rank two over `𝒪`. -/
private theorem free_of_mem_maximalIdeal [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    (hϖ : ϖ ∈ IsLocalRing.maximalIdeal 𝒪) (hϖ0 : ϖ ≠ 0) : Module.Free T T := by
  have := isLocalRing hϖ
  have := (g_monic ϖ).free_adjoinRoot
  have := (g_monic ϖ).finite_adjoinRoot
  exact Module.free_of_torsionBySet_eq_annihilator_smul (πT ϖ) (congruenceIdeal_ne_bot hϖ0)
    (pairing ϖ) (pairing_balanced ϖ) (bijective_pairing ϖ) T (pairing ϖ)
    (fun t m n => pairing_balanced ϖ t m n) (bijective_pairing ϖ)
    (by rw [finrank_torsion, one_mul]) (torsionBySet_self_eq _)

end RankTwo

/-- A concrete instance with `T ≠ 𝒪`: `𝒪 = ℤ_[2]` and `ϖ = 2`. -/
example : Module.Free (AdjoinRoot (g (2 : ℤ_[2]))) (AdjoinRoot (g (2 : ℤ_[2]))) :=
  free_of_mem_maximalIdeal
    (by rw [PadicInt.maximalIdeal_eq_span_p]; exact_mod_cast Ideal.mem_span_singleton_self _)
    two_ne_zero

end FreeOfBalancedPairingTest

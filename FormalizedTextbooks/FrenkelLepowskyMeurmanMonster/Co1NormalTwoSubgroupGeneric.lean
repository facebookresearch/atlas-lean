/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.PGroup

/-! Fixed-space argument excluding normal 2-subgroups from faithful irreducible binary actions. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The vectors fixed by every element of a specified subgroup in a binary linear action. -/
def binarySubgroupFixedSpace {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : G →* (V ≃ₗ[ZMod 2] V)) (P : Subgroup G) : Submodule (ZMod 2) V where
  carrier := {v | ∀ p : P, ρ p.val v = v}
  zero_mem' p := map_zero _
  add_mem' hv hw p := by rw [map_add, hv p, hw p]
  smul_mem' a v hv p := by rw [map_smul, hv p]

/-- Normality makes the subgroup's fixed space invariant under the entire linear action. -/
theorem binarySubgroupFixedSpace_invariant {G V : Type*}
    [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : G →* (V ≃ₗ[ZMod 2] V)) (P : Subgroup G) [P.Normal]
    (g : G) (v : V) (hv : v ∈ binarySubgroupFixedSpace ρ P) :
    ρ g v ∈ binarySubgroupFixedSpace ρ P := by
  intro p
  have hq : g⁻¹ * p.val * g ∈ P := by
    simpa only [inv_inv] using (inferInstance : P.Normal).conj_mem p.val p.property g⁻¹
  let q : P := ⟨g⁻¹ * p.val * g, hq⟩
  change (ρ p.val * ρ g) v = ρ g v
  rw [← map_mul, show p.val * g = g * (g⁻¹ * p.val * g) by simp [mul_assoc], map_mul]
  change ρ g (ρ q.val v) = ρ g v
  rw [hv q]

/-- A finite nonzero binary vector space has even cardinality. -/
theorem binaryModule_two_dvd_card {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V] [Nontrivial V] :
    2 ∣ Nat.card V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV : IsPGroup 2 (Multiplicative V) := by
    intro v
    refine ⟨1, ?_⟩
    simp only [pow_one, pow_two]
    change v.toAdd + v.toAdd = 0
    have h := two_smul (ZMod 2) v.toAdd
    rw [show (2 : ZMod 2) = 0 by decide, zero_smul] at h
    exact h.symm
  obtain ⟨n, hn⟩ := hV.exists_card_eq
  have hn0 : n ≠ 0 := by
    intro hz
    rw [hz, pow_zero] at hn
    have hpos : 1 < Nat.card (Multiplicative V) :=
      Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    omega
  have h := dvd_pow_self 2 hn0
  rw [← hn] at h
  exact h

/-- A 2-subgroup acting linearly on a finite nonzero binary space fixes a nonzero vector. -/
theorem binarySubgroupFixedSpace_nonzero {G V : Type*}
    [Group G] [AddCommGroup V] [Module (ZMod 2) V] [Finite V] [Nontrivial V]
    (ρ : G →* (V ≃ₗ[ZMod 2] V)) (P : Subgroup G) (hP : IsPGroup 2 P) :
    binarySubgroupFixedSpace ρ P ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : MulAction P V := MulAction.compHom V (ρ.comp P.subtype)
  have hz : (0 : V) ∈ MulAction.fixedPoints P V := by
    intro p
    exact map_zero (ρ p.val)
  obtain ⟨v, hv, hne⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point V
    binaryModule_two_dvd_card hz
  intro he
  have hfixed : v ∈ binarySubgroupFixedSpace ρ P := hv
  rw [he, Submodule.mem_bot] at hfixed
  exact hne hfixed.symm

/-- A faithful irreducible finite binary representation has no nontrivial normal 2-subgroup. -/
theorem faithful_irreducible_binary_normal_two_subgroup_eq_bot {G V : Type*}
    [Group G] [AddCommGroup V] [Module (ZMod 2) V] [Finite V] [Nontrivial V]
    (ρ : G →* (V ≃ₗ[ZMod 2] V)) (hfaithful : Function.Injective ρ)
    (hirreducible : ∀ W : Submodule (ZMod 2) V,
      (∀ g v, v ∈ W → ρ g v ∈ W) → W = ⊥ ∨ W = ⊤)
    (P : Subgroup G) [P.Normal] (hP : IsPGroup 2 P) : P = ⊥ := by
  have htop : binarySubgroupFixedSpace ρ P = ⊤ :=
    (hirreducible _ (binarySubgroupFixedSpace_invariant ρ P)).resolve_left
      (binarySubgroupFixedSpace_nonzero ρ P hP)
  apply (Subgroup.eq_bot_iff_forall P).mpr
  intro p hp
  apply hfaithful
  rw [map_one]
  apply LinearEquiv.ext
  intro v
  have hv : v ∈ binarySubgroupFixedSpace ρ P := by rw [htop]; trivial
  exact hv ⟨p, hp⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

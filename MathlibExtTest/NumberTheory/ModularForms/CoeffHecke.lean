/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.CoeffHecke
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.Tactic.NormNum

@[expose] public section

open scoped MatrixGroups

open groupCohomology

namespace MathlibExtTest.NumberTheory.ModularForms.CoeffHecke

/-- Consumer with the public theorem's binders. -/
theorem exactSource
    (N ℓ ℓ' m : ℕ) [NeZero ℓ] [NeZero ℓ'] [NeZero m] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (hℓℓ' : ¬ ℓ ∣ ℓ') (hm : m = ℓ * ℓ')
    {K : Type} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K (CongruenceSubgroup.Gamma0 N) V) (a a' : V →ₗ[K] V)
    (ha : ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
      a ∘ₗ ρ (HeckeEis.heckeConj N ℓ u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a)
    (ha' : ∀ u : ↥(HeckeEis.heckeUpper N ℓ'),
      a' ∘ₗ ρ (HeckeEis.heckeConj N ℓ' u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a')
    {z : CongruenceSubgroup.Gamma0 N → V} (hz : z ∈ cocycles₁ (Rep.of ρ)) :
    HeckeEis.coeffHeckeFun N ℓ ρ a (HeckeEis.coeffHeckeFun N ℓ' ρ a' z)
      - HeckeEis.coeffHeckeFun N m ρ (a ∘ₗ a') z ∈ coboundaries₁ (Rep.of ρ) :=
  HeckeEis.coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coboundaries₁
    N ℓ ℓ' m hℓ hℓN hℓℓ' hm ρ a a' ha ha' hz

/-- The theorem composes with Mathlib's `H¹`: the composite of the Hecke
operators at `ℓ'` and `ℓ` and the Hecke operator at `m` give a cocycle the
same class. -/
example
    (N ℓ ℓ' m : ℕ) [NeZero ℓ] [NeZero ℓ'] [NeZero m] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (hℓℓ' : ¬ ℓ ∣ ℓ') (hm : m = ℓ * ℓ')
    {K V : Type} [CommRing K] [AddCommGroup V] [Module K V]
    (ρ : Representation K (CongruenceSubgroup.Gamma0 N) V) (a a' : V →ₗ[K] V)
    (ha : ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
      a ∘ₗ ρ (HeckeEis.heckeConj N ℓ u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a)
    (ha' : ∀ u : ↥(HeckeEis.heckeUpper N ℓ'),
      a' ∘ₗ ρ (HeckeEis.heckeConj N ℓ' u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a')
    {z : CongruenceSubgroup.Gamma0 N → V} (hz : z ∈ cocycles₁ (Rep.of ρ)) :
    H1π (Rep.of ρ) (⟨_, HeckeEis.coeffHeckeFun_mem_cocycles₁ N ℓ ρ a ha
        (HeckeEis.coeffHeckeFun_mem_cocycles₁ N ℓ' ρ a' ha' hz)⟩ : cocycles₁ (Rep.of ρ)) =
      H1π (Rep.of ρ) (⟨_, HeckeEis.coeffHeckeFun_mem_cocycles₁ N m ρ (a ∘ₗ a')
        (HeckeEis.heckeConj_intertwines_comp hm ρ ha ha') hz⟩ : cocycles₁ (Rep.of ρ)) :=
  (H1π_eq_iff _ _).2 <|
    HeckeEis.coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coboundaries₁
      N ℓ ℓ' m hℓ hℓN hℓℓ' hm ρ a a' ha ha' hz

/-- Non-vacuity: every hypothesis holds together for `N = 4`, `ℓ = 3`, `ℓ' = 2`,
`m = 6`, the representation of `Gamma0 4` on `ℚ` by `χ₄` of the lower-right
entry (the conjugation keeps that entry, so `a = a' = id` intertwine), and the
cocycle `z g = χ₄ (g 1 1) - 1`, which is not zero: `z (-1) = -2`. -/
example :
    let ρ : Representation ℚ (CongruenceSubgroup.Gamma0 4) ℚ :=
      (Algebra.lmul ℚ ℚ : ℚ →* Module.End ℚ ℚ).comp ((Int.castRingHom ℚ : ℤ →* ℚ).comp
        ((ZMod.χ₄ : ZMod 4 →* ℤ).comp (CongruenceSubgroup.Gamma0Map 4)))
    let z : CongruenceSubgroup.Gamma0 4 → ℚ := fun g => ρ g 1 - 1
    z ⟨-1, by simp [CongruenceSubgroup.Gamma0_mem]⟩ = -2 ∧
      HeckeEis.coeffHeckeFun 4 3 ρ LinearMap.id (HeckeEis.coeffHeckeFun 4 2 ρ LinearMap.id z)
        - HeckeEis.coeffHeckeFun 4 6 ρ (LinearMap.id ∘ₗ LinearMap.id) z ∈
          coboundaries₁ (Rep.of ρ) := by
  intro ρ z
  refine ⟨?_, HeckeEis.coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coboundaries₁
    4 3 2 6 Nat.prime_three (by decide) (by decide) rfl ρ LinearMap.id LinearMap.id
    (fun _ => rfl) (fun _ => rfl) (coboundaries₁_le_cocycles₁ _ ⟨1, rfl⟩)⟩
  change ((ZMod.χ₄ (-1 : ZMod 4) : ℤ) : ℚ) * 1 - 1 = -2
  rw [show ZMod.χ₄ (-1 : ZMod 4) = -1 by decide]
  norm_num

end MathlibExtTest.NumberTheory.ModularForms.CoeffHecke

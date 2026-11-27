/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Finiteness
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.Group

/-!
# Intersecting a retract of a free group with a finitely generated subgroup

We refute the proposed retract intersection property using the three-generator subgroup of the
rank-two free group in §3 of Snopce, Tanushevski and Zalesskii, *Retracts of Free Groups and a
Question of Bergman*.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.RetractIntersectionFreeGroupKourovka17Problem19Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.19 (G. M.
Bergman). UnsolvedMath record UM-00701321 (`KOU-17.19`), dataset ulamai/UnsolvedMath v1.8.0.

`R` is a retract of `F` when some endomorphism of `F` has image `R` and fixes `R` pointwise. `F =
FreeGroup (Fin n)`; a subgroup of a free group has finite rank exactly when it is finitely
generated, so `H` is required to be finitely generated.
-/

/-- **Retract of a group.** A subgroup $R$ of a group $F$ is a retract of $F$ when there is an
endomorphism $r \colon F \to F$ whose image is $R$ and which fixes every element of $R$. -/
def IsRetract {F : Type*} [Group F] (R : Subgroup F) : Prop :=
  ∃ r : F →* F, r.range = R ∧ ∀ x ∈ R, r x = x

/-- **Bergman's retract intersection question (Kourovka Problem 17.19).** The statement that for
every natural number $n$, every retract $R$ of the free group $F_n$ on $n$ generators and every
finitely generated subgroup $H$ of $F_n$, the intersection $H \cap R$ is a retract of $H$.

A subgroup of a free group is finitely generated exactly when it has finite rank. -/
def retractIntersectionIsRetract : Prop :=
  ∀ (n : ℕ) (R H : Subgroup (FreeGroup (Fin n))), IsRetract R → H.FG →
    IsRetract ((H ⊓ R).subgroupOf H)

open scoped commutatorElement

private abbrev F := FreeGroup (Fin 2)

private def x : F := FreeGroup.of 0
private def y : F := FreeGroup.of 1
private def w : F := x * ⁅x, y⁆
private def t₁ : F := y * x * (y ^ 2)⁻¹
private def t₂ : F := y ^ 2 * x * y⁻¹
private def H : Subgroup F := Subgroup.closure {x, t₁, t₂}

private def exponent : F →* Multiplicative ℤ :=
  FreeGroup.lift fun i => if i = 0 then Multiplicative.ofAdd 1 else 1

private theorem exponent_w : exponent w = Multiplicative.ofAdd 1 := by
  simp [w, x, y, commutatorElement_def, exponent]

private theorem cyclic_isRetract : IsRetract (Subgroup.zpowers w) := by
  let p := (zpowersHom F w).comp exponent
  have hfix (z : ℤ) : p (w ^ z) = w ^ z := by
    simp [p, exponent_w]
  refine ⟨p, le_antisymm ?_ ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩
    exact Subgroup.zpow_mem_zpowers w _
  · rintro _ ⟨z, rfl⟩
    exact ⟨w ^ z, hfix z⟩
  · rintro _ ⟨z, rfl⟩
    exact hfix z

-- In the action x = (1 2), y = (0 1 2), the generators of H fix 0 and w moves it.
private theorem w_not_mem : w ∉ H := by
  let σ : F →* Equiv.Perm (Fin 3) := FreeGroup.lift fun i =>
    if i = 0 then Equiv.swap 1 2 else Equiv.swap 0 1 * Equiv.swap 1 2
  have hH : H ≤ (MulAction.stabilizer (Equiv.Perm (Fin 3)) (0 : Fin 3)).comap σ := by
    apply (Subgroup.closure_le _).mpr
    intro a ha
    rcases ha with (rfl | rfl | rfl) <;>
      change σ _ 0 = 0 <;>
      simp only [σ, x, y, t₁, t₂, map_mul, map_pow, map_inv, FreeGroup.lift_apply_of] <;> decide
  have hmoves : σ w 0 ≠ 0 := by
    simp only [σ, w, x, y, commutatorElement_def, map_mul, map_inv, FreeGroup.lift_apply_of]
    decide
  exact fun hw => hmoves (hH hw)

private theorem intersection_not_isRetract :
    ¬ IsRetract ((H ⊓ Subgroup.zpowers w).subgroupOf H) := by
  rintro ⟨r, hr, hfix⟩
  let a : H := ⟨x, Subgroup.subset_closure (by simp)⟩
  let b : H := ⟨t₁, Subgroup.subset_closure (by simp)⟩
  let c : H := ⟨t₂, Subgroup.subset_closure (by simp)⟩
  let v := a ^ 2 * ⁅c⁻¹, b⁆
  have hv : (v : F) = w ^ 2 := by
    change x ^ 2 * ⁅t₂⁻¹, t₁⁆ = w ^ 2
    simp only [w, t₁, t₂, commutatorElement_def, pow_two]
    group
  have hrv : r v = v := by
    refine hfix v ⟨v.property, ?_⟩
    change (v : F) ∈ Subgroup.zpowers w
    rw [hv]
    exact Subgroup.npow_mem_zpowers w 2
  have hra : r a ∈ (H ⊓ Subgroup.zpowers w).subgroupOf H := by
    rw [← hr]
    exact ⟨a, rfl⟩
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hra.2
  -- The exponent sum kills the commutator, so fixing v forces r(a) to have exponent one.
  let e := (exponent.comp H.subtype).comp r
  have he : exponent (w ^ 2) = exponent (w ^ m) ^ 2 := calc
    exponent (w ^ 2) = e v := by
      change _ = exponent (r v : F)
      rw [hrv, hv]
    _ = e a ^ 2 := by
      simp [v, map_commutatorElement, commutatorElement_eq_one_iff_commute, Commute.all]
    _ = exponent (w ^ m) ^ 2 := by
      rw [hm]
      rfl
  have he' := congrArg Multiplicative.toAdd he
  simp only [map_pow, map_zpow, exponent_w, Int.toAdd_pow, Int.toAdd_zpow,
    toAdd_ofAdd, one_mul] at he'
  have hm' : m = 1 := by omega
  apply w_not_mem
  rw [hm', zpow_one] at hm
  rw [hm]
  exact (r a).property

/--
**Negative answer to Bergman's retract intersection question (Kourovka Problem 17.19).** It is not
the case that for every natural number $n$, every retract $R$ of the free group $F_n$ on $n$
generators and every finitely generated subgroup $H$ of $F_n$, the intersection $H \cap R$ is a
retract of $H$.

Snopce, Tanushevski and Zalesskii (2022) give a free group $F$ of finite rank, a retract $R$ of $F$
and a finitely generated subgroup $H$ of $F$ such that $H \cap R$ is not a retract of $H$; the
Kourovka Archive answers 17.19 "No, it need not".

Source: E. I. Khukhro and
V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.19 (G. M. Bergman); resolution: I.
Snopce, S. Tanushevski and P. Zalesskii, Int. Math. Res. Notices 2022, no. 11 (2022), 8280-8294,
Kourovka Archive, Problem 17.19 (No, it need not).
-/
theorem retractIntersectionIsRetract_refuted : ¬ retractIntersectionIsRetract := by
  intro h
  have hfg : H.FG := H.fg_iff.mpr ⟨_, rfl, ((Set.finite_singleton t₂).insert t₁).insert x⟩
  exact intersection_not_isRetract (h 2 _ H cyclic_isRetract hfg)

end MathlibExt.GroupTheory.RetractIntersectionFreeGroupKourovka17Problem19Wanted

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightQSupportUpper
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightParityNonzero
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthQTriviality

/-! Genuine tensor and odd-short witnesses sharpen the original full-axis Q-kernel bounds. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The actual remaining original quotient bits form a genuine homomorphism on full-axis fixers. -/
def generatedFifthRootEightQKernelProjection : generatedFifthRootEightAxisQStabilizer →*
    Multiplicative (Fin 2 → ZMod 2) where
  toFun q := ofAdd (generatedFifthRootEightQSupportFreeMatrix *ᵥ toAdd q.val.base)
  map_one' := by
    apply toAdd.injective
    change generatedFifthRootEightQSupportFreeMatrix *ᵥ toAdd (1 : Q).base = 0
    simp
  map_mul' q r := by
    apply toAdd.injective
    change generatedFifthRootEightQSupportFreeMatrix *ᵥ toAdd (q.val * r.val).base =
      generatedFifthRootEightQSupportFreeMatrix *ᵥ toAdd q.val.base +
        generatedFifthRootEightQSupportFreeMatrix *ᵥ toAdd r.val.base
    rw [NormalizedCocycleExtension.mul_base, toAdd_mul, Matrix.mulVec_add]

/-- The actual nonzero tensor eliminates every central ambiguity in the original quotient. -/
theorem generatedFifthRootEight_Q_kernel_projection_injective :
    Function.Injective generatedFifthRootEightQKernelProjection := by
  intro q r h
  have he := congrArg (fun v : Multiplicative (Fin 2 → ZMod 2) =>
    generatedFifthRootEightQSupportFreeProjection *ᵥ toAdd v) h
  change generatedFifthRootEightQSupportFreeProjection *ᵥ
      (generatedFifthRootEightQSupportFreeMatrix *ᵥ toAdd q.val.base) =
    generatedFifthRootEightQSupportFreeProjection *ᵥ
      (generatedFifthRootEightQSupportFreeMatrix *ᵥ toAdd r.val.base) at he
  rw [generatedFifthRootEight_Q_support_free_quotient q.val q.property,
    generatedFifthRootEight_Q_support_free_quotient r.val r.property] at he
  have hb : toAdd (q.val * r.val⁻¹).base = 0 := by
    rw [NormalizedCocycleExtension.mul_base, NormalizedCocycleExtension.inv_base,
      toAdd_mul, toAdd_inv, he, add_neg_cancel]
  have hf : rhoLocal (inclQ (q.val * r.val⁻¹)) generatedFifthRootEightAxis =
      generatedFifthRootEightAxis :=
    (q * r⁻¹).property
  have hq := generatedTenth_Q_eq_one_of_zero_quotient generatedFifthRootEightAxis _ hf hb
    generatedFifthRootEight_outgoing_tensor_ne_zero
  exact Subtype.ext (mul_inv_eq_one.mp hq)

/-- The first free original quotient column is literally the Omega direction. -/
theorem generatedFifthRootEight_Q_kernel_Omega_column :
    generatedFifthRootEightQSupportFreeProjection *ᵥ (Pi.single (0 : Fin 2) 1) =
      Pi.single (11 : Fin 24) 1 := by
  decide +kernel

/-- A genuine supported odd coordinate excludes the entire Omega coset from the kernel image. -/
theorem generatedFifthRootEight_Q_kernel_Omega_not_mem :
    ofAdd (Pi.single (0 : Fin 2) (1 : ZMod 2)) ∉
      generatedFifthRootEightQKernelProjection.range := by
  rintro ⟨q, hq⟩
  have hb := congrArg (fun v : Multiplicative (Fin 2 → ZMod 2) =>
    generatedFifthRootEightQSupportFreeProjection *ᵥ toAdd v) hq
  change generatedFifthRootEightQSupportFreeProjection *ᵥ
      (generatedFifthRootEightQSupportFreeMatrix *ᵥ toAdd q.val.base) =
    generatedFifthRootEightQSupportFreeProjection *ᵥ (Pi.single (0 : Fin 2) 1) at hb
  rw [generatedFifthRootEight_Q_support_free_quotient q.val q.property,
    generatedFifthRootEight_Q_kernel_Omega_column] at hb
  have hz := generatedTenth_Q_quotient_zero_of_Omega generatedFifthRootEightAxis q.val q.property 1
    (by simpa only [one_smul] using hb) generatedFifthRootEight_odd_short_exists_nonzero
  have hc := congrFun (hb.symm.trans hz) (11 : Fin 24)
  change (1 : ZMod 2) = 0 at hc
  exact one_ne_zero hc

/-- All genuine original full-axis Q fixers have at most two elements. -/
theorem generatedFifthRootEight_axis_Q_kernel_upper_two :
    Nat.card generatedFifthRootEightAxisQStabilizer ≤ 2 := by
  let : Finite (Multiplicative (Fin 2 → ZMod 2)) := inferInstance
  have hi0 := generatedFifthRootEightQKernelProjection.range.index_ne_zero_of_finite
  have hi1 : generatedFifthRootEightQKernelProjection.range.index ≠ 1 := by
    intro hi
    have ht := (Subgroup.index_eq_one).mp hi
    apply generatedFifthRootEight_Q_kernel_Omega_not_mem
    rw [ht]
    exact Subgroup.mem_top _
  have hi : 2 ≤ generatedFifthRootEightQKernelProjection.range.index := by omega
  have hc := generatedFifthRootEightQKernelProjection.range.card_mul_index
  have hgroup : Nat.card (Multiplicative (Fin 2 → ZMod 2)) = 4 := by
    norm_num [Nat.card_eq_fintype_card]
  rw [hgroup] at hc
  have hle := Nat.mul_le_mul_left (Nat.card generatedFifthRootEightQKernelProjection.range) hi
  rw [hc] at hle
  have hb : Nat.card generatedFifthRootEightQKernelProjection.range ≤ 2 := by omega
  have he := Nat.card_congr
    (MonoidHom.ofInjective generatedFifthRootEight_Q_kernel_projection_injective).toEquiv
  rw [he]
  exact hb

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

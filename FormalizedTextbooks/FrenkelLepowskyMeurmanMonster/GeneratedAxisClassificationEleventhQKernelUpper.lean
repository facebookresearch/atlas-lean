/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEleventhQSupportUpper
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEleventhTensorNonzero
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEleventhQRootFixed
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthQTriviality

/-! Genuine tensor and odd-short witnesses sharpen the original full-axis Q-kernel bounds. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The actual remaining original quotient bits form a genuine homomorphism on full-axis fixers. -/
def generatedEleventhQKernelProjection : generatedEleventhAxisQStabilizer →*
    Multiplicative (Fin 3 → ZMod 2) where
  toFun q := ofAdd (generatedEleventhQSupportFreeMatrix *ᵥ toAdd q.val.base)
  map_one' := by
    apply toAdd.injective
    change generatedEleventhQSupportFreeMatrix *ᵥ toAdd (1 : Q).base = 0
    simp
  map_mul' q r := by
    apply toAdd.injective
    change generatedEleventhQSupportFreeMatrix *ᵥ toAdd (q.val * r.val).base =
      generatedEleventhQSupportFreeMatrix *ᵥ toAdd q.val.base +
        generatedEleventhQSupportFreeMatrix *ᵥ toAdd r.val.base
    rw [NormalizedCocycleExtension.mul_base, toAdd_mul, Matrix.mulVec_add]

/-- The actual nonzero tensor eliminates every central ambiguity in the original quotient. -/
theorem generatedEleventh_Q_kernel_projection_injective :
    Function.Injective generatedEleventhQKernelProjection := by
  intro q r h
  have he := congrArg (fun v : Multiplicative (Fin 3 → ZMod 2) =>
    generatedEleventhQSupportFreeProjection *ᵥ toAdd v) h
  change generatedEleventhQSupportFreeProjection *ᵥ
      (generatedEleventhQSupportFreeMatrix *ᵥ toAdd q.val.base) =
    generatedEleventhQSupportFreeProjection *ᵥ
      (generatedEleventhQSupportFreeMatrix *ᵥ toAdd r.val.base) at he
  rw [generatedEleventh_Q_support_free_quotient q.val q.property,
    generatedEleventh_Q_support_free_quotient r.val r.property] at he
  have hb : toAdd (q.val * r.val⁻¹).base = 0 := by
    rw [NormalizedCocycleExtension.mul_base, NormalizedCocycleExtension.inv_base,
      toAdd_mul, toAdd_inv, he, add_neg_cancel]
  have hf : rhoLocal (inclQ (q.val * r.val⁻¹)) generatedEleventhAxis = generatedEleventhAxis :=
    (q * r⁻¹).property
  have hq := generatedTenth_Q_eq_one_of_zero_quotient generatedEleventhAxis _ hf hb
    generatedEleventh_tensor_ne_zero
  exact Subtype.ext (mul_inv_eq_one.mp hq)

/-- The first free original quotient column is literally the Omega direction. -/
theorem generatedEleventh_Q_kernel_Omega_column :
    generatedEleventhQSupportFreeProjection *ᵥ (Pi.single (0 : Fin 3) 1) =
      Pi.single (11 : Fin 24) 1 := by
  decide +kernel

/-- A genuine supported odd coordinate excludes the entire Omega coset from the kernel image. -/
theorem generatedEleventh_Q_kernel_Omega_not_mem :
    ofAdd (Pi.single (0 : Fin 3) (1 : ZMod 2)) ∉
      generatedEleventhQKernelProjection.range := by
  rintro ⟨q, hq⟩
  have hb := congrArg (fun v : Multiplicative (Fin 3 → ZMod 2) =>
    generatedEleventhQSupportFreeProjection *ᵥ toAdd v) hq
  change generatedEleventhQSupportFreeProjection *ᵥ
      (generatedEleventhQSupportFreeMatrix *ᵥ toAdd q.val.base) =
    generatedEleventhQSupportFreeProjection *ᵥ (Pi.single (0 : Fin 3) 1) at hb
  rw [generatedEleventh_Q_support_free_quotient q.val q.property,
    generatedEleventh_Q_kernel_Omega_column] at hb
  have hz := generatedTenth_Q_quotient_zero_of_Omega generatedEleventhAxis q.val q.property 1
    (by simpa only [one_smul] using hb) generatedEleventh_odd_short_exists_nonzero
  have hc := congrFun (hb.symm.trans hz) (11 : Fin 24)
  change (1 : ZMod 2) = 0 at hc
  exact one_ne_zero hc

/-- All genuine original full-axis Q fixers have at most four elements. -/
theorem generatedEleventh_axis_Q_kernel_upper_four :
    Nat.card generatedEleventhAxisQStabilizer ≤ 4 := by
  let : Finite (Multiplicative (Fin 3 → ZMod 2)) := inferInstance
  have hi0 := generatedEleventhQKernelProjection.range.index_ne_zero_of_finite
  have hi1 : generatedEleventhQKernelProjection.range.index ≠ 1 := by
    intro hi
    have ht := (Subgroup.index_eq_one).mp hi
    apply generatedEleventh_Q_kernel_Omega_not_mem
    rw [ht]
    exact Subgroup.mem_top _
  have hi : 2 ≤ generatedEleventhQKernelProjection.range.index := by omega
  have hc := generatedEleventhQKernelProjection.range.card_mul_index
  have hgroup : Nat.card (Multiplicative (Fin 3 → ZMod 2)) = 8 := by
    norm_num [Nat.card_eq_fintype_card]
  rw [hgroup] at hc
  have hle := Nat.mul_le_mul_left (Nat.card generatedEleventhQKernelProjection.range) hi
  rw [hc] at hle
  have hb : Nat.card generatedEleventhQKernelProjection.range ≤ 4 := by omega
  have he := Nat.card_congr
    (MonoidHom.ofInjective generatedEleventh_Q_kernel_projection_injective).toEquiv
  rw [he]
  exact hb

/-- The complete original full-axis kernel has at least two actual elements. -/
theorem generatedEleventh_axis_Q_kernel_lower_two :
    2 ≤ Nat.card generatedEleventhAxisQStabilizer := by
  let f : Bool → generatedEleventhAxisQStabilizer := fun b =>
    if b then ⟨generatedEleventhRootQ, generatedEleventh_root_Q_fixed⟩ else 1
  have hf : Function.Injective f := by
    intro b c h
    cases b <;> cases c
    · rfl
    · have he := congrArg Subtype.val h
      exact False.elim (generatedEleventh_root_Q_ne_one he.symm)
    · have he := congrArg Subtype.val h
      exact False.elim (generatedEleventh_root_Q_ne_one he)
    · rfl
  have h := Nat.card_le_card_of_injective f hf
  norm_num [Nat.card_eq_fintype_card] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

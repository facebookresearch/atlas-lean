/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

import MathlibExt.Algebra.Category.ModuleCat.TorsionFunctor
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Module.ULift
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.NormNum

/-!
# Actual primary components in a larger coefficient universe

The coefficient is the lifted product Z/4 x Z. For I=(4), its primary
component contains (1,0) but excludes (0,1), so it is genuinely a proper
nonzero submodule. The actual restricted map 3 times the identity sends
(1,0) to (3,0). Native degree-zero derived torsion uses the existing
enough-injectives instance, not a supplied comparison or inverse.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace TorsionFunctorIndependentUniversesTest

private def I : Ideal ℤ := Ideal.span ({4} : Set ℤ)

private def M : ModuleCat.{1} ℤ := ModuleCat.of ℤ (ULift.{1} (ZMod 4 × ℤ))

private def originalOne : M := ULift.up (1, 0)

private def originalFreeOne : M := ULift.up (0, 1)

private theorem originalOne_mem :
    originalOne ∈ Ideal.primaryComponent (M : Type 1) I := by
  apply (ModuleCat.Torsion.mem_obj_iff I M originalOne).mpr
  refine ⟨1, ?_⟩
  intro r hr
  rw [pow_one] at hr
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hr
  change s * 4 = r at hs
  subst r
  apply ULift.ext
  apply Prod.ext
  · change (s * 4 : ℤ) • (1 : ZMod 4) = 0
    rw [mul_smul]
    have h4 : (4 : ℤ) • (1 : ZMod 4) = 0 := by
      rw [← Int.cast_smul_eq_zsmul (R := ZMod 4)]
      change (4 : ZMod 4) • (1 : ZMod 4) = 0
      have hcast : (4 : ZMod 4) = 0 := by decide
      rw [hcast, zero_smul]
    rw [h4, smul_zero]
  · change (s * 4 : ℤ) • (0 : ℤ) = 0
    exact smul_zero _

private def torsionOne : (ModuleCat.Torsion.functor I).obj M :=
  ⟨originalOne, originalOne_mem⟩

private theorem primary_component_proper :
    originalFreeOne ∉ Ideal.primaryComponent (M : Type 1) I := by
  intro h
  obtain ⟨n, hn⟩ := (ModuleCat.Torsion.mem_obj_iff I M originalFreeOne).mp h
  have h4 : (4 : ℤ) ∈ I := Ideal.mem_span_singleton_self 4
  have hz := hn (4 ^ n) (Ideal.pow_mem_pow h4 n)
  have hfree := congrArg (fun m : M => m.down.2) hz
  change (4 : ℤ) ^ n • (1 : ℤ) = 0 at hfree
  have hfree' : (4 : ℤ) ^ n = 0 := by
    change ((4 : ℤ) ^ n) * (1 : ℤ) = 0 at hfree
    exact (mul_one ((4 : ℤ) ^ n)).symm.trans hfree
  exact (pow_ne_zero n (by norm_num : (4 : ℤ) ≠ 0)) hfree'

private theorem inclusion_detects_one :
    (((ModuleCat.Torsion.inclusion I).app M).hom torsionOne).down.1 = (1 : ZMod 4) := rfl

private theorem restricted_three_value :
    ((((ModuleCat.Torsion.functor I).map ((3 : ℤ) • 𝟙 M)).hom torsionOne).val).down.1 =
      (3 : ZMod 4) := by
  rw [ModuleCat.Torsion.map_val]
  change (3 : ℤ) • (1 : ZMod 4) = (3 : ZMod 4)
  rw [← Int.cast_smul_eq_zsmul (R := ZMod 4)]
  exact mul_one _

private theorem restricted_three_nonzero :
    ((ModuleCat.Torsion.functor I).map ((3 : ℤ) • 𝟙 M)).hom torsionOne ≠ 0 := by
  intro h
  have hv := congrArg (fun a : (ModuleCat.Torsion.functor I).obj M => a.val.down.1) h
  rw [restricted_three_value] at hv
  change (3 : ZMod 4) = 0 at hv
  exact (by decide : (3 : ZMod 4) ≠ 0) hv

private theorem actual_zero_degree_triangle :
    (ModuleCat.Torsion.toLocalCohomologyZero I).app M ≫
      (ModuleCat.Torsion.localCohomologyZeroIso I).hom.app M =
        𝟙 ((ModuleCat.Torsion.functor I).obj M) := by
  have h := congrArg
    (fun α : (ModuleCat.Torsion.functor I : ModuleCat.{1} ℤ ⥤ ModuleCat.{1} ℤ) ⟶
      ModuleCat.Torsion.functor I => α.app M)
    (ModuleCat.Torsion.toLocalCohomologyZero_comp_zeroIso I)
  simpa only [NatTrans.comp_app, NatTrans.id_app] using h

end TorsionFunctorIndependentUniversesTest

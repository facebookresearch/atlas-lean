/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The intrinsic tensor multiplication trace form of the actual centralizer. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerBlocks
public import Mathlib.LinearAlgebra.Trace

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Restrict an actual centralizer element to the involution's fixed space. -/
noncomputable def generatedCentralizerPlusEquiv (g : generatedCentralizer) :
    generatedCentralPlus ≃ₗ[ℝ] generatedCentralPlus where
  toFun x := ⟨g.val.val x, generatedCentralizer_preserves_plus g x x.property⟩
  invFun x := ⟨(g⁻¹).val.val x, generatedCentralizer_preserves_plus (g⁻¹) x x.property⟩
  left_inv x := by
    apply Subtype.ext
    change g.val.val.symm (g.val.val x.val) = x.val
    exact g.val.val.symm_apply_apply _
  right_inv x := by
    apply Subtype.ext
    change g.val.val (g.val.val.symm x.val) = x.val
    exact g.val.val.apply_symm_apply _
  map_add' x y := Subtype.ext (g.val.val.map_add _ _)
  map_smul' a x := Subtype.ext (g.val.val.map_smul a x.val)

/-- Restrict the same actual element to the negative tensor space. -/
noncomputable def generatedCentralizerMinusEquiv (g : generatedCentralizer) :
    generatedCentralMinus ≃ₗ[ℝ] generatedCentralMinus where
  toFun x := ⟨g.val.val x, generatedCentralizer_preserves_minus g x x.property⟩
  invFun x := ⟨(g⁻¹).val.val x, generatedCentralizer_preserves_minus (g⁻¹) x x.property⟩
  left_inv x := by
    apply Subtype.ext
    change g.val.val.symm (g.val.val x.val) = x.val
    exact g.val.val.symm_apply_apply _
  right_inv x := by
    apply Subtype.ext
    change g.val.val (g.val.val.symm x.val) = x.val
    exact g.val.val.apply_symm_apply _
  map_add' x y := Subtype.ext (g.val.val.map_add _ _)
  map_smul' a x := Subtype.ext (g.val.val.map_smul a x.val)

/-- Multiplication by an actual fixed vector, restricted to actual negative vectors. -/
noncomputable def generatedCentralTensorMul (u : generatedCentralPlus) :
    generatedCentralMinus →ₗ[ℝ] generatedCentralMinus where
  toFun x := ⟨griessProd u.val x.val, generatedCentralPlus_mul_minus u.val x.val
    u.property x.property⟩
  map_add' x y := Subtype.ext ((griessProd u.val).map_add x.val y.val)
  map_smul' a x := Subtype.ext ((griessProd u.val).map_smul a x.val)

set_option maxRecDepth 4096 in
/-- Actual centralizer multiplication intertwines its tensor restriction. -/
theorem generatedCentralTensorMul_conjugate (g : generatedCentralizer)
    (u : generatedCentralPlus) :
    generatedCentralTensorMul (generatedCentralizerPlusEquiv g u) =
      (generatedCentralizerMinusEquiv g).conj (generatedCentralTensorMul u) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change griessProd (g.val.val u.val) x.val =
    g.val.val (griessProd u.val (g.val.val.symm x.val))
  rw [generated_group_preserves_griessProduct sExtra_preserves_griessProd]
  rw [LinearEquiv.apply_symm_apply]

/-- The intrinsic bilinear form obtained from multiplication on the negative eigenspace. -/
noncomputable def generatedCentralTensorTraceForm (u v : generatedCentralPlus) : ℝ :=
  LinearMap.trace ℝ generatedCentralMinus
    ((generatedCentralTensorMul u).comp (generatedCentralTensorMul v))

private theorem linearConjugate_comp {V : Type*} [AddCommGroup V] [Module ℝ V]
    (e : V ≃ₗ[ℝ] V) (a b : V →ₗ[ℝ] V) :
    (e.conj a).comp (e.conj b) = e.conj (a.comp b) := by
  ext x
  change e (a (e.symm (e (b (e.symm x))))) = e (a (b (e.symm x)))
  rw [LinearEquiv.symm_apply_apply]

/-- Every element of the full actual centralizer preserves this trace form.
This invariance uses the proved multiplication, not an assumption about its constituents. -/
theorem generatedCentralizer_preserves_tensorTraceForm (g : generatedCentralizer)
    (u v : generatedCentralPlus) :
    generatedCentralTensorTraceForm (generatedCentralizerPlusEquiv g u)
      (generatedCentralizerPlusEquiv g v) = generatedCentralTensorTraceForm u v := by
  unfold generatedCentralTensorTraceForm
  rw [generatedCentralTensorMul_conjugate, generatedCentralTensorMul_conjugate,
    linearConjugate_comp, LinearMap.trace_conj']

/-- Physical spin coordinates identify the actual negative space with the actual tensor space. -/
noncomputable def generatedCentralMinusTensorEquiv :
    generatedCentralMinus ≃ₗ[ℝ] (SpinIndex → Fin 24 → ℝ) where
  toFun x := (griessConwayEncode x.val).2.2
  invFun T := ⟨griessConwayDecode (0, (0, T)), by
    rw [mem_generatedCentralMinus_iff_matrix_short_zero,
      griessConwayEncode_decode _ (by intros; rfl)]
    exact ⟨rfl,rfl⟩⟩
  left_inv x := by
    apply Subtype.ext
    have hx := (mem_generatedCentralMinus_iff_matrix_short_zero x.val).mp x.property
    have he : ((0, (0, (griessConwayEncode x.val).2.2)) : ConwayRawSpace) =
        griessConwayEncode x.val := Prod.ext hx.1.symm (Prod.ext hx.2.symm rfl)
    change griessConwayDecode (0, (0, (griessConwayEncode x.val).2.2)) = x.val
    rw [he, griessConwayDecode_encode]
  right_inv T := by
    have he := griessConwayEncode_decode ((0, (0, T)) : ConwayRawSpace) (by intros; rfl)
    exact congrArg (fun x : ConwayRawSpace => x.2.2) he
  map_add' x y := by
    have he := griessConwayEncodeLinear.map_add x.val y.val
    exact congrArg (fun x : ConwayRawSpace => x.2.2) he
  map_smul' a x := by
    have he := griessConwayEncodeLinear.map_smul a x.val
    exact congrArg (fun x : ConwayRawSpace => x.2.2) he

/-- The actual negative eigenspace has the source dimension 98304. -/
theorem generatedCentralMinus_finrank : Module.finrank ℝ generatedCentralMinus = 98304 := by
  rw [generatedCentralMinusTensorEquiv.finrank_eq]
  simp [Module.finrank_pi_fintype, SpinIndex, Fintype.card_pi, Fintype.card_fin, ZMod.card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

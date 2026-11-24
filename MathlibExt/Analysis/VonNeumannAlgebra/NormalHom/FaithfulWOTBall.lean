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

public import MathlibExt.Analysis.VonNeumannAlgebra.NormalHom.FaithfulBallImage
public import MathlibExt.Analysis.VonNeumannAlgebra.UltraweakWOT

/-!
# Actual faithful normal operator-range balls are WOT compact and closed

The existing compact ultraweak range ball maps continuously to the original
weak operator carrier. Its image is exactly the original concrete operator
range intersected with the same norm ball. Thus that literal intersection
is WOT compact and closed, including arbitrary radii and zero Hilbert
spaces. No closed-range, weak topology or compactness certificate is input.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Topology

namespace VonNeumannAlgebra.NormalStarAlgHom

noncomputable section

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}

/-- Each literal norm ball in the actual faithful normal operator range is WOT compact. -/
theorem wot_range_inter_ball_isCompact (f : NormalStarAlgHom M N)
    (hf : Function.Injective f) (r : ℝ) :
    IsCompact {q : K →WOT[ℂ] K |
      q.toCLM ∈ Set.range (fun x : M => (f x : K →L[ℂ] K)) ∧ ‖q.toCLM‖ ≤ r} := by
  let W : Ultraweak N → (K →WOT[ℂ] K) :=
    fun y => ContinuousLinearMapWOT.ofCLM (ultraweakLinearEquiv N y : K →L[ℂ] K)
  have hW : Continuous W := ultraweak_toWOT_continuous N
  have hWvalue (y : Ultraweak N) : (W y).toCLM = (ultraweakLinearEquiv N y : K →L[ℂ] K) :=
    ContinuousLinearMapWOT.toCLM_ofCLM _
  have hcompact := (f.ultraweak_range_inter_ball_isCompact hf r).image hW
  have hset : W '' (Set.range f.ultraweakMap ∩ {y : Ultraweak N | ‖ultraweakLinearEquiv N y‖ ≤ r}) =
      {q : K →WOT[ℂ] K |
        q.toCLM ∈ Set.range (fun x : M => (f x : K →L[ℂ] K)) ∧ ‖q.toCLM‖ ≤ r} := by
    ext q
    constructor
    · rintro ⟨y, ⟨⟨x, rfl⟩, hy⟩, rfl⟩
      have hvalue : ultraweakLinearEquiv N (f.ultraweakMap x) = f (ultraweakLinearEquiv M x) := by
        rw [f.ultraweakMap_apply, LinearEquiv.apply_symm_apply]
      refine ⟨⟨ultraweakLinearEquiv M x, ?_⟩, ?_⟩
      · rw [hWvalue, hvalue]
      · rw [hWvalue]
        exact hy
    · rintro ⟨⟨x, hx⟩, hn⟩
      change (f x : K →L[ℂ] K) = q.toCLM at hx
      refine ⟨(ultraweakLinearEquiv N).symm (f x),
        ⟨⟨(ultraweakLinearEquiv M).symm x, ?_⟩, ?_⟩, ?_⟩
      · rw [f.ultraweakMap_apply, LinearEquiv.apply_symm_apply]
      · change ‖ultraweakLinearEquiv N ((ultraweakLinearEquiv N).symm (f x))‖ ≤ r
        rw [LinearEquiv.apply_symm_apply]
        change ‖(f x : K →L[ℂ] K)‖ ≤ r
        rw [hx]
        exact hn
      · apply ContinuousLinearMapWOT.toCLM_injective
        rw [hWvalue, LinearEquiv.apply_symm_apply]
        exact hx
  rw [← hset]
  exact hcompact

/-- The same literal faithful range norm ball is closed in the original WOT carrier. -/
theorem isClosed_wot_range_inter_ball (f : NormalStarAlgHom M N)
    (hf : Function.Injective f) (r : ℝ) :
    IsClosed {q : K →WOT[ℂ] K |
      q.toCLM ∈ Set.range (fun x : M => (f x : K →L[ℂ] K)) ∧ ‖q.toCLM‖ ≤ r} :=
  (f.wot_range_inter_ball_isCompact hf r).isClosed

end

end VonNeumannAlgebra.NormalStarAlgHom

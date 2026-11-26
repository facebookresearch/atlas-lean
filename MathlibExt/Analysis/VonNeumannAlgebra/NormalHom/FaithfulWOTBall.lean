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
# Weak-operator compact balls in an injective normal range

For an injective normal unital complex star homomorphism `f : M → N`, let `R ⊆ B(K)` be its
operator range. For every real `r`, `{T ∈ R : ‖T‖≤r}` is compact and closed in the weak operator
topology of `B(K)`.

The bound uses the target operator norm. Negative radii give the empty set; no nonzero-space or
global range-closedness premise is needed.
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

/-- **WOT compactness of a bounded injective normal range.** Let `M,N` be concrete von Neumann
algebras on complete complex Hilbert spaces. Their normal-functional Banach spaces
`M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak topologies
are `σ(M,M_*)`, `σ(N,N_*)`. Let `f : M → N` be a unital complex star homomorphism that is
ultraweakly continuous. Assume `f` is injective. Write `R={ (f(x) : B(K)) : x ∈ M }` for
its operator range on the target Hilbert space `K`. for every `r : ℝ`, `{T ∈ B(K) : T∈R ∧
‖T‖≤r}` is compact in the weak operator topology. -/
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

/-- **WOT closedness of a bounded injective normal range.** Let `M,N` be concrete von Neumann
algebras on complete complex Hilbert spaces. Their normal-functional Banach spaces
`M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak topologies
are `σ(M,M_*)`, `σ(N,N_*)`. Let `f : M → N` be a unital complex star homomorphism that is
ultraweakly continuous. Assume `f` is injective. Write `R={ (f(x) : B(K)) : x ∈ M }` for
its operator range on the target Hilbert space `K`. for every `r : ℝ`, `{T ∈ B(K) : T∈R ∧
‖T‖≤r}` is closed in the weak operator topology. -/
theorem isClosed_wot_range_inter_ball (f : NormalStarAlgHom M N)
    (hf : Function.Injective f) (r : ℝ) :
    IsClosed {q : K →WOT[ℂ] K |
      q.toCLM ∈ Set.range (fun x : M => (f x : K →L[ℂ] K)) ∧ ‖q.toCLM‖ ≤ r} :=
  (f.wot_range_inter_ball_isCompact hf r).isClosed

end

end VonNeumannAlgebra.NormalStarAlgHom

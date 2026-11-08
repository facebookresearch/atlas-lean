/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
public import Mathlib.Analysis.InnerProductSpace.Dual

import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Tactic.FunProp
import Mathlib.Topology.Order.Basic

/-!
# Céa's lemma for the Galerkin method

Let `V` be a real Hilbert space, let `B : V →L[ℝ] V →L[ℝ] ℝ` be a bounded
bilinear form that is coercive, and let `L : V →L[ℝ] ℝ` be a bounded linear
functional. The *variational problem* is to find `u : V` such that
`B u w = L w` for all `w : V`. The *Galerkin problem* in a complete subspace
`W ⊆ V` is to find `u_h ∈ W` such that `B u_h w = L w` for all `w ∈ W`.

This file proves existence and uniqueness for both problems (from the
Lax–Milgram theorem in `Mathlib`), Galerkin orthogonality, and **Céa's
lemma**: the Galerkin error is bounded by `(‖B‖ / α)` times the
best-approximation error, where `α` is a coercivity constant for `B`:

* `variationalSolution`, `galerkinSolution`: the solutions of the two problems.
* `galerkin_orthogonality`: `B (u - u_h) w = 0` for all `w ∈ W`.
* `norm_sub_galerkinSolution_le`: Céa's lemma in pointwise form.
* `norm_sub_galerkinSolution_le_iInf`: Céa's lemma in infimum form.

No symmetry of `B` is assumed anywhere: Céa's lemma only needs coercivity
and boundedness. This is a companion to the Hilbert-space material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean` (the
projection theorem, the Riesz representation theorem). It is not one of the
72 v1 targets, and Céa's lemma / the Galerkin method are not in the pinned
Mathlib (which has the Lax–Milgram theorem but no Galerkin approximation) or
in base MathlibExt.
-/

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.CeaLemma

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- For real `a`, `a ≤ ‖a‖`. -/
private theorem le_norm_self_real (a : ℝ) : a ≤ ‖a‖ := by
  rw [Real.norm_eq_abs]
  exact le_abs_self a

/-- Restriction of a bounded bilinear form to a submodule. -/
noncomputable def restrictBilin (B : V →L[ℝ] V →L[ℝ] ℝ) (W : Submodule ℝ V) :
    W →L[ℝ] W →L[ℝ] ℝ where
  toFun x := (B x).comp W.subtypeL
  map_add' x y := by
    ext z
    simp [map_add]
  map_smul' c x := by
    ext z
    simp [map_smul]
  cont := by
    fun_prop

@[simp]
theorem restrictBilin_apply (B : V →L[ℝ] V →L[ℝ] ℝ) (W : Submodule ℝ V)
    (x y : W) : restrictBilin B W x y = B (x : V) (y : V) := rfl

/-- Coercivity is inherited by restriction to a submodule. -/
theorem isCoercive_restrictBilin {B : V →L[ℝ] V →L[ℝ] ℝ} {W : Submodule ℝ V}
    (hB : IsCoercive B) : IsCoercive (restrictBilin B W) := by
  obtain ⟨C, hC, hco⟩ := hB
  exact ⟨C, hC, fun x => by simpa [restrictBilin_apply] using hco (x : V)⟩

/-- The solution of the variational problem `B u w = L w` for all `w`,
obtained from the Lax–Milgram equivalence and the Riesz representation. -/
noncomputable def variationalSolution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hB : IsCoercive B) (L : E →L[ℝ] ℝ) : E :=
  hB.continuousLinearEquivOfBilin.symm ((InnerProductSpace.toDual ℝ E).symm L)

/-- The variational solution satisfies the variational equation. -/
theorem variationalSolution_spec {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hB : IsCoercive B) (L : E →L[ℝ] ℝ) (w : E) :
    B (variationalSolution hB L) w = L w := by
  have h1 : (hB.continuousLinearEquivOfBilin
      (variationalSolution hB L)) = (InnerProductSpace.toDual ℝ E).symm L := by
    simp [variationalSolution]
  have h2 : inner ℝ (hB.continuousLinearEquivOfBilin (variationalSolution hB L)) w
      = B (variationalSolution hB L) w :=
    IsCoercive.continuousLinearEquivOfBilin_apply hB _ _
  rw [h1] at h2
  rw [← h2]
  exact InnerProductSpace.toDual_symm_apply

/-- Uniqueness for the variational problem: two vectors satisfying the same
variational equation agree, by coercivity. -/
theorem eq_of_forall_bilin {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hB : IsCoercive B) {L : E →L[ℝ] ℝ} {x y : E}
    (hx : ∀ w, B x w = L w) (hy : ∀ w, B y w = L w) : x = y := by
  obtain ⟨α, hα, hco⟩ := hB
  have h0 : B (x - y) (x - y) = 0 := by
    have h : ∀ w, B (x - y) w = 0 := by
      intro w
      have hsub : B (x - y) w = B x w - B y w := by
        rw [map_sub]
        simp
      rw [hsub, hx w, hy w, sub_self]
    exact h (x - y)
  have hle := hco (x - y)
  rw [h0] at hle
  have hsq : ‖x - y‖ * ‖x - y‖ ≤ 0 := by
    have h2 : α * (‖x - y‖ * ‖x - y‖) ≤ α * 0 := by
      rw [mul_zero]
      calc α * (‖x - y‖ * ‖x - y‖) = α * ‖x - y‖ * ‖x - y‖ := by ring
        _ ≤ 0 := hle
    exact le_of_mul_le_mul_left h2 hα
  have hzero : ‖x - y‖ * ‖x - y‖ = 0 :=
    le_antisymm hsq (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hnorm : ‖x - y‖ = 0 := mul_self_eq_zero.mp hzero
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- The variational solution is the unique solution of the variational
equation. -/
theorem variationalSolution_eq_of_forall {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hB : IsCoercive B) {L : E →L[ℝ] ℝ} {x : E}
    (hx : ∀ w, B x w = L w) : x = variationalSolution hB L :=
  eq_of_forall_bilin hB hx (variationalSolution_spec hB L)

/-- Existence for the variational problem, in bare existential form. -/
theorem exists_variationalSolution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hB : IsCoercive B) (L : E →L[ℝ] ℝ) : ∃ u, ∀ w, B u w = L w :=
  ⟨variationalSolution hB L, variationalSolution_spec hB L⟩

/-- If `α * ‖x‖ * ‖x‖ ≤ M * ‖x‖` with `0 < α` and `0 ≤ M`, then `‖x‖ ≤ M / α`.
This is the division step shared by the stability estimates below. -/
private theorem norm_le_div_of_sq_le {E : Type*} [NormedAddCommGroup E]
    {x : E} {α M : ℝ} (hα : 0 < α) (hM : 0 ≤ M)
    (h : α * ‖x‖ * ‖x‖ ≤ M * ‖x‖) : ‖x‖ ≤ M / α := by
  by_cases hn : ‖x‖ = 0
  · rw [hn]
    exact div_nonneg hM hα.le
  · have hpos : 0 < ‖x‖ := lt_of_le_of_ne' (norm_nonneg _) hn
    have h1 : α * ‖x‖ ≤ M := by
      have hle : (α * ‖x‖) * ‖x‖ ≤ M * ‖x‖ := by
        calc (α * ‖x‖) * ‖x‖ = α * ‖x‖ * ‖x‖ := by ring
          _ ≤ M * ‖x‖ := h
      exact le_of_mul_le_mul_right hle hpos
    rw [le_div_iff₀ hα]
    calc ‖x‖ * α = α * ‖x‖ := mul_comm _ _
      _ ≤ M := h1

/-- The Galerkin solution in `W`: the solution of the variational problem
for the restricted form and the restricted functional. -/
noncomputable def galerkinSolution {B : V →L[ℝ] V →L[ℝ] ℝ} (hB : IsCoercive B)
    {W : Submodule ℝ V} (hW : IsComplete (W : Set V)) (L : V →L[ℝ] ℝ) : W :=
  @variationalSolution W _ _ hW.completeSpace_coe _
    (isCoercive_restrictBilin hB) (L.comp W.subtypeL)

/-- The Galerkin solution satisfies the Galerkin equations. -/
theorem galerkinSolution_spec {B : V →L[ℝ] V →L[ℝ] ℝ} (hB : IsCoercive B)
    {W : Submodule ℝ V} (hW : IsComplete (W : Set V)) (L : V →L[ℝ] ℝ) (w : W) :
    B (galerkinSolution hB hW L : V) (w : V) = L (w : V) := by
  have h := @variationalSolution_spec W _ _ hW.completeSpace_coe _
    (isCoercive_restrictBilin (B := B) (W := W) hB) (L.comp W.subtypeL) w
  simpa [galerkinSolution, restrictBilin_apply] using h

/-- The Galerkin solution is the unique element of `W` satisfying the
Galerkin equations. -/
theorem galerkinSolution_eq_of_forall {B : V →L[ℝ] V →L[ℝ] ℝ} (hB : IsCoercive B)
    {W : Submodule ℝ V} (hW : IsComplete (W : Set V)) {L : V →L[ℝ] ℝ} {x : W}
    (hx : ∀ w : W, B (x : V) (w : V) = L (w : V)) : x = galerkinSolution hB hW L := by
  have h1 : ∀ w : W, restrictBilin B W x w = (L.comp W.subtypeL) w := by
    intro w
    simpa [restrictBilin_apply] using hx w
  have h2 : ∀ w : W, restrictBilin B W (galerkinSolution hB hW L) w
      = (L.comp W.subtypeL) w := by
    intro w
    simpa [restrictBilin_apply] using galerkinSolution_spec hB hW L w
  exact @eq_of_forall_bilin W _ _ _ (isCoercive_restrictBilin hB)
    (L.comp W.subtypeL) _ _ h1 h2

/-- Existence for the Galerkin problem, in bare existential form. -/
theorem exists_galerkinSolution {B : V →L[ℝ] V →L[ℝ] ℝ} (hB : IsCoercive B)
    {W : Submodule ℝ V} (hW : IsComplete (W : Set V)) (L : V →L[ℝ] ℝ) :
    ∃ uh ∈ W, ∀ w ∈ W, B uh w = L w := by
  refine ⟨(galerkinSolution hB hW L : V), (galerkinSolution hB hW L).2, fun w hw => ?_⟩
  exact galerkinSolution_spec hB hW L ⟨w, hw⟩

variable [CompleteSpace V]

/-- Galerkin orthogonality: the error `u - u_h` is `B`-orthogonal to `W`. -/
theorem galerkin_orthogonality {B : V →L[ℝ] V →L[ℝ] ℝ} (hB : IsCoercive B)
    {W : Submodule ℝ V} (hW : IsComplete (W : Set V)) (L : V →L[ℝ] ℝ) (w : W) :
    B (variationalSolution hB L - (galerkinSolution hB hW L : V)) (w : V) = 0 := by
  have hu := variationalSolution_spec hB L (w : V)
  have hg := galerkinSolution_spec hB hW L w
  have hsub : B (variationalSolution hB L - (galerkinSolution hB hW L : V)) (w : V)
      = B (variationalSolution hB L) (w : V)
        - B (galerkinSolution hB hW L : V) (w : V) := by
    rw [map_sub]
    simp
  rw [hsub, hu, hg, sub_self]

/-- **Céa's lemma** (pointwise form): the Galerkin error is bounded by
`(‖B‖ / α)` times the distance from `u` to any element `v` of `W`. -/
theorem norm_sub_galerkinSolution_le {B : V →L[ℝ] V →L[ℝ] ℝ} (hB : IsCoercive B)
    {W : Submodule ℝ V} (hW : IsComplete (W : Set V)) (L : V →L[ℝ] ℝ)
    {α : ℝ} (hα : 0 < α) (hco : ∀ v, α * ‖v‖ * ‖v‖ ≤ B v v) (v : V) (hv : v ∈ W) :
    ‖variationalSolution hB L - (galerkinSolution hB hW L : V)‖
      ≤ (‖B‖ / α) * ‖variationalSolution hB L - v‖ := by
  set u := variationalSolution hB L with hu_def
  set uh : V := (galerkinSolution hB hW L : V) with huh_def
  set e := u - uh with he_def
  have hort : B e (uh - v) = 0 := by
    have h := galerkin_orthogonality hB hW L ⟨uh - v, sub_mem (galerkinSolution hB hW L).2 hv⟩
    simpa [he_def] using h
  have hsplit : B e e = B e (u - v) := by
    have hdecomp : e = (u - v) - (uh - v) := by
      simp [he_def, sub_sub]
    have h1 : B e ((u - v) - (uh - v)) = B e (u - v) - B e (uh - v) :=
      map_sub (B e) _ _
    have h2 : B e e = B e ((u - v) - (uh - v)) := congrArg (fun z => B e z) hdecomp
    rw [h2, h1, hort, sub_zero]
  have hbound : B e (u - v) ≤ ‖B‖ * ‖e‖ * ‖u - v‖ := by
    calc B e (u - v) ≤ ‖B e (u - v)‖ := le_norm_self_real _
      _ ≤ ‖B‖ * ‖e‖ * ‖u - v‖ := ContinuousLinearMap.le_opNorm₂ B e (u - v)
  have hmain : α * ‖e‖ * ‖e‖ ≤ (‖B‖ * ‖u - v‖) * ‖e‖ := by
    calc α * ‖e‖ * ‖e‖ ≤ B e e := hco e
      _ = B e (u - v) := hsplit
      _ ≤ ‖B‖ * ‖e‖ * ‖u - v‖ := hbound
      _ = (‖B‖ * ‖u - v‖) * ‖e‖ := by ring
  rw [div_mul_eq_mul_div]
  exact norm_le_div_of_sq_le (M := ‖B‖ * ‖u - v‖) hα
    (mul_nonneg (norm_nonneg B) (norm_nonneg (u - v))) hmain

/-- **Céa's lemma** (infimum form): the Galerkin error is bounded by
`(‖B‖ / α)` times the best-approximation error `⨅ v : W, ‖u - v‖`. -/
theorem norm_sub_galerkinSolution_le_iInf {B : V →L[ℝ] V →L[ℝ] ℝ} (hB : IsCoercive B)
    {W : Submodule ℝ V} (hW : IsComplete (W : Set V)) (L : V →L[ℝ] ℝ)
    {α : ℝ} (hα : 0 < α) (hco : ∀ v, α * ‖v‖ * ‖v‖ ≤ B v v) :
    ‖variationalSolution hB L - (galerkinSolution hB hW L : V)‖
      ≤ (‖B‖ / α) * ⨅ v : W, ‖variationalSolution hB L - (v : V)‖ := by
  have hc : 0 ≤ ‖B‖ / α := div_nonneg (norm_nonneg B) hα.le
  rw [Real.mul_iInf_of_nonneg hc]
  refine le_ciInf fun v => ?_
  exact norm_sub_galerkinSolution_le hB hW L hα hco (v : V) v.2

/-- Stability of the variational solution: `‖u‖ ≤ ‖L‖ / α`. -/
theorem norm_variationalSolution_le {B : V →L[ℝ] V →L[ℝ] ℝ} (hB : IsCoercive B)
    (L : V →L[ℝ] ℝ) {α : ℝ} (hα : 0 < α) (hco : ∀ v, α * ‖v‖ * ‖v‖ ≤ B v v) :
    ‖variationalSolution hB L‖ ≤ ‖L‖ / α := by
  set u := variationalSolution hB L with hu_def
  have hspec := variationalSolution_spec hB L u
  have hmain : α * ‖u‖ * ‖u‖ ≤ ‖L‖ * ‖u‖ := by
    calc α * ‖u‖ * ‖u‖ ≤ B u u := hco u
      _ = L u := hspec
      _ ≤ ‖L u‖ := le_norm_self_real _
      _ ≤ ‖L‖ * ‖u‖ := L.le_opNorm u
  exact norm_le_div_of_sq_le (M := ‖L‖) hα (norm_nonneg _) hmain

omit [CompleteSpace V] in
/-- Stability of the Galerkin solution: `‖u_h‖ ≤ ‖L‖ / α`. -/
theorem norm_galerkinSolution_le {B : V →L[ℝ] V →L[ℝ] ℝ} (hB : IsCoercive B)
    {W : Submodule ℝ V} (hW : IsComplete (W : Set V)) (L : V →L[ℝ] ℝ)
    {α : ℝ} (hα : 0 < α) (hco : ∀ v, α * ‖v‖ * ‖v‖ ≤ B v v) :
    ‖galerkinSolution hB hW L‖ ≤ ‖L‖ / α := by
  have hspec := galerkinSolution_spec hB hW L (galerkinSolution hB hW L)
  have hmain : α * ‖(galerkinSolution hB hW L : V)‖ * ‖(galerkinSolution hB hW L : V)‖
      ≤ ‖L‖ * ‖(galerkinSolution hB hW L : V)‖ := by
    calc α * ‖(galerkinSolution hB hW L : V)‖ * ‖(galerkinSolution hB hW L : V)‖
          ≤ B (galerkinSolution hB hW L : V) (galerkinSolution hB hW L : V) :=
        hco _
      _ = L (galerkinSolution hB hW L : V) := hspec
      _ ≤ ‖L (galerkinSolution hB hW L : V)‖ := le_norm_self_real _
      _ ≤ ‖L‖ * ‖(galerkinSolution hB hW L : V)‖ := L.le_opNorm _
  have h := norm_le_div_of_sq_le (E := V) (M := ‖L‖) hα (norm_nonneg _) hmain
  rwa [Submodule.norm_coe] at h

end MathlibExt.Analysis.InnerProductSpace.CeaLemma

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Uniform
public import Mathlib.Analysis.Normed.Module.DoubleDual
import MathlibExt.Analysis.FunctionalAnalysis.BanachSpace
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

@[expose] public section

section

namespace MathlibExt.Analysis.FunctionalAnalysis.MilmanPettisWanted

/-- Rotation step: a norm-one double-dual vector attains real part close to one
on some functional of the unit ball. -/
private theorem exists_re_gt
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {Ψ : StrongDual 𝕜 (StrongDual 𝕜 E)} (hΨ : ‖Ψ‖ = 1)
    {δ : ℝ} (hδpos : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ f : StrongDual 𝕜 E, ‖f‖ ≤ 1 ∧ 1 - δ / 2 < RCLike.re (Ψ f) := by
  have ht : 1 - δ / 2 < ‖Ψ‖ := by
    rw [hΨ]
    linarith
  obtain ⟨g, hg1, hg2⟩ := Ψ.exists_lt_apply_of_lt_opNorm ht
  have hpos : 0 < ‖Ψ g‖ := by
    have h05 : (0 : ℝ) < 1 - δ / 2 := by
      linarith
    exact lt_of_lt_of_le h05 hg2.le
  set z : 𝕜 := Ψ g with hzdef
  have hzpos : 0 < ‖z‖ := hpos
  have hznorm_ne : ((‖z‖ : ℝ) : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr hzpos.ne'
  set u : 𝕜 := starRingEnd 𝕜 z / (‖z‖ : 𝕜) with hudef
  have hu1 : ‖u‖ = 1 := by
    rw [hudef, norm_div, RCLike.norm_conj, RCLike.norm_ofReal,
      abs_of_pos hzpos, div_self hzpos.ne']
  refine ⟨u • g, ?_, ?_⟩
  · rw [norm_smul, hu1, one_mul]
    exact hg1.le
  · have e1 : Ψ (u • g) = u * z := by
      rw [map_smul, smul_eq_mul]
    have hcc : starRingEnd 𝕜 z * z = (((‖z‖ : ℝ) : 𝕜) ^ 2) :=
      RCLike.conj_mul z
    have e2 : u * z = ((‖z‖ : ℝ) : 𝕜) := by
      rw [hudef, div_mul_eq_mul_div, hcc, pow_two,
        mul_div_cancel_left₀ _ hznorm_ne]
    rw [e1, e2, RCLike.ofReal_re]
    exact hg2

/-- Every norm-one double-dual vector is within `ε₀` in norm of the canonical
image of the unit ball. -/
private theorem approx_of_norm_one
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [UniformConvexSpace E]
    {Ψ : StrongDual 𝕜 (StrongDual 𝕜 E)} (hΨ : ‖Ψ‖ = 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ x₀ : E, ‖Ψ - (NormedSpace.inclusionInDoubleDual 𝕜 E) x₀‖ ≤ ε₀ := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ :=
    exists_forall_closed_ball_dist_add_le_two_sub E hε₀
  set δ : ℝ := min δ₀ 1 with hδdef
  have hδpos : 0 < δ := lt_min hδ₀pos one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδ : ∀ ⦃x : E⦄, ‖x‖ ≤ 1 → ∀ ⦃y⦄, ‖y‖ ≤ 1 →
      ε₀ ≤ ‖x - y‖ → ‖x + y‖ ≤ 2 - δ := by
    intro x hx y hy hxy
    calc ‖x + y‖ ≤ 2 - δ₀ := hδ₀ hx hy hxy
      _ ≤ 2 - δ := by
        apply sub_le_sub_left _ _
        rw [hδdef]
        exact min_le_left _ _
  obtain ⟨f, hf1, hfre⟩ := exists_re_gt hΨ hδpos hδ1
  set J := NormedSpace.inclusionInDoubleDual 𝕜 E with hJdef
  set S : Set (WeakDual 𝕜 (StrongDual 𝕜 E)) :=
    (StrongDual.toWeakDual ∘ J) '' Metric.closedBall (0 : E) 1 with hSdef
  set V : Set (WeakDual 𝕜 (StrongDual 𝕜 E)) :=
    {Θ | 1 - δ / 2 < RCLike.re (Θ f)} with hVdef
  have hVopen : IsOpen V := by
    rw [hVdef]
    exact isOpen_lt continuous_const
      (RCLike.continuous_re.comp (WeakDual.eval_continuous f))
  have hΨS : StrongDual.toWeakDual Ψ ∈ closure S := by
    have hGold := MetaMathlibExt.goldstine (𝕜 := 𝕜) (E := E)
    have hmem : StrongDual.toWeakDual Ψ ∈ WeakDual.toStrongDual ⁻¹'
        Metric.closedBall (0 : StrongDual 𝕜 (StrongDual 𝕜 E)) 1 := by
      simp only [Set.mem_preimage, StrongDual.toStrongDual_toWeakDual]
      apply Metric.mem_closedBall.mpr
      have e : dist Ψ 0 = ‖Ψ‖ := dist_zero_right Ψ
      rw [e]
      exact hΨ.le
    rw [hSdef, hJdef, hGold]
    exact hmem
  have hΨV : StrongDual.toWeakDual Ψ ∈ V := by
    rw [hVdef]
    simp only [Set.mem_ofPred_eq, StrongDual.toWeakDual_apply]
    exact hfre
  have hVS : (V ∩ S).Nonempty := by
    have hnbhd : V ∈ nhds (StrongDual.toWeakDual Ψ) :=
      hVopen.mem_nhds hΨV
    exact mem_closure_iff_nhds.mp hΨS V hnbhd
  obtain ⟨Θ₀, hΘ₀V, hΘ₀S⟩ := hVS
  rw [hSdef] at hΘ₀S
  obtain ⟨x₀, hx₀ball, hΘ₀eq⟩ := hΘ₀S
  have hx₀norm : ‖x₀‖ ≤ 1 := by
    have h := Metric.mem_closedBall.mp hx₀ball
    rwa [dist_zero_right] at h
  have hx₀V : 1 - δ / 2 < RCLike.re (f x₀) := by
    have h := hΘ₀V
    rw [hVdef] at h
    simp only [Set.mem_ofPred_eq] at h
    rw [← hΘ₀eq] at h
    simp only [Function.comp_apply, StrongDual.toWeakDual_apply, hJdef,
      NormedSpace.dual_def] at h
    exact h
  have key : ∀ x : E, ‖x‖ ≤ 1 →
      1 - δ / 2 < RCLike.re (f x) → ‖x - x₀‖ < ε₀ := by
    intro x hxn hxr
    by_contra hcon
    push Not at hcon
    have hle := hδ hxn hx₀norm hcon
    have hsum : 2 - δ < ‖x + x₀‖ := by
      have h1 : RCLike.re (f (x + x₀)) ≤ ‖x + x₀‖ := by
        calc RCLike.re (f (x + x₀)) ≤ ‖f (x + x₀)‖ :=
              RCLike.re_le_norm _
          _ ≤ ‖f‖ * ‖x + x₀‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ 1 * ‖x + x₀‖ := by
              apply mul_le_mul_of_nonneg_right hf1 (norm_nonneg _)
          _ = ‖x + x₀‖ := one_mul _
      have heq : RCLike.re (f (x + x₀))
          = RCLike.re (f x) + RCLike.re (f x₀) := by
        simp only [map_add]
      linarith
    linarith
  set T : Set (WeakDual 𝕜 (StrongDual 𝕜 E)) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall (J x₀) ε₀ with hTdef
  have hTclosed : IsClosed T := by
    rw [hTdef]
    exact WeakDual.isClosed_closedBall _ _
  have hsub : V ∩ S ⊆ T := by
    intro Θ hΘ
    obtain ⟨hΘV, hΘS⟩ := hΘ
    rw [hSdef] at hΘS
    obtain ⟨x, hxball, hΘeq⟩ := hΘS
    have hxn : ‖x‖ ≤ 1 := by
      have h := Metric.mem_closedBall.mp hxball
      rwa [dist_zero_right] at h
    have hxr : 1 - δ / 2 < RCLike.re (f x) := by
      have h := hΘV
      rw [hVdef] at h
      simp only [Set.mem_ofPred_eq] at h
      rw [← hΘeq] at h
      simp only [Function.comp_apply, StrongDual.toWeakDual_apply, hJdef,
        NormedSpace.dual_def] at h
      exact h
    have hlt : ‖x - x₀‖ < ε₀ := key x hxn hxr
    rw [hTdef]
    simp only [Set.mem_preimage]
    have hΘ : WeakDual.toStrongDual Θ = J x := by
      rw [← hΘeq]
      simp only [Function.comp_apply, StrongDual.toStrongDual_toWeakDual]
    rw [hΘ]
    apply Metric.mem_closedBall.mpr
    have hdist : dist (J x) (J x₀) = dist x x₀ :=
      (NormedSpace.inclusionInDoubleDualLi 𝕜 (E := E)).dist_map x x₀
    have e : dist x x₀ = ‖x - x₀‖ := dist_eq_norm x x₀
    rw [hdist, e]
    exact hlt.le
  have hΨmem2 : StrongDual.toWeakDual Ψ ∈ closure (V ∩ S) := by
    have hmem : StrongDual.toWeakDual Ψ ∈ V ∩ closure S := ⟨hΨV, hΨS⟩
    exact hVopen.inter_closure hmem
  have hΨT : StrongDual.toWeakDual Ψ ∈ T :=
    closure_minimal hsub hTclosed hΨmem2
  rw [hTdef] at hΨT
  simp only [Set.mem_preimage, StrongDual.toStrongDual_toWeakDual] at hΨT
  have hdist : dist Ψ (J x₀) ≤ ε₀ := Metric.mem_closedBall.mp hΨT
  have e : dist Ψ (J x₀) = ‖Ψ - J x₀‖ := dist_eq_norm Ψ (J x₀)
  rw [e] at hdist
  exact ⟨x₀, hdist⟩

/-- Milman-Pettis for norm-one double-dual vectors: the vector lies in the norm
closure of the range of the canonical embedding, and the range is closed. -/
private theorem milman_pettis_aux
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [UniformConvexSpace E]
    [CompleteSpace E]
    {Φ : StrongDual 𝕜 (StrongDual 𝕜 E)} (hΦ : ‖Φ‖ = 1) :
    ∃ x : E, ∀ (f : StrongDual 𝕜 E), Φ f = f x := by
  set J := NormedSpace.inclusionInDoubleDual 𝕜 E with hJdef
  have hmem : Φ ∈ closure (Set.range J) := by
    apply (SeminormedAddCommGroup.mem_closure_iff (s := Set.range J)
      (a := Φ)).mpr
    intro ε hε
    have hε2 : (0 : ℝ) < ε / 2 := by
      linarith
    obtain ⟨x₀, hx₀⟩ := approx_of_norm_one hΦ hε2
    rw [← hJdef] at hx₀
    refine ⟨J x₀, ⟨x₀, rfl⟩, ?_⟩
    linarith
  have hclosed : IsClosed (Set.range J) := by
    have h1 :=
      (NormedSpace.inclusionInDoubleDualLi 𝕜 (E := E)).isometry
    have h2 := h1.isUniformInducing
    have hli : IsComplete
        (Set.range (NormedSpace.inclusionInDoubleDualLi 𝕜 (E := E))) :=
      h2.isComplete_range
    have hrange : Set.range (NormedSpace.inclusionInDoubleDualLi 𝕜 (E := E))
        = Set.range J := by
      rw [hJdef]
      ext y
      simp only [Set.mem_range]
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x, rfl⟩
      · rintro ⟨x, rfl⟩
        exact ⟨x, rfl⟩
    rw [hrange] at hli
    exact hli.isClosed
  rw [hclosed.closure_eq] at hmem
  obtain ⟨y, hy⟩ := hmem
  refine ⟨y, fun f => ?_⟩
  have h : J y f = Φ f := by
    rw [hy]
  rw [hJdef, NormedSpace.dual_def] at h
  exact h.symm

/--
**Milman–Pettis theorem.** Let $E$ be a uniformly convex Banach space over $\mathbb{K} = \mathbb{R}$
or $\mathbb{C}$, and let $E^*$ be the space of continuous linear functionals on $E$. Then every
continuous linear functional $\Phi$ on $E^*$ is evaluation at a point: there is $x \in E$ with
$\Phi(f) = f(x)$ for every $f \in E^*$.

Proves `Wanted` entry `milman_pettis`.

Source: D. Milman, C. R. (Doklady) Acad. Sci. URSS 18 (1938) and B. Pettis, Duke Math. J. 1939,
Milman-Pettis theorem that uniformly convex Banach spaces are reflexive; Clarkson uniform
convexity 1936; Lean states `RCLike` uniformly convex complete case via double-dual evaluation
surjectivity.
-/
theorem milman_pettis
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [UniformConvexSpace E] [CompleteSpace E]
    (Φ : (E →L[𝕜] 𝕜) →L[𝕜] 𝕜) :
    ∃ x : E, ∀ (f : E →L[𝕜] 𝕜), Φ f = f x := by
  by_cases hΦ0 : Φ = 0
  · refine ⟨0, fun f => ?_⟩
    rw [hΦ0]
    simp only [zero_apply, map_zero]
  · have hcposCLM : 0 < ‖Φ‖ := by
      by_contra hcon
      push Not at hcon
      have hzero : ‖Φ‖ = 0 :=
        le_antisymm hcon (ContinuousLinearMap.opNorm_nonneg Φ)
      have hΦeq : Φ = 0 := by
        ext f
        simp only [zero_apply]
        have hle := ContinuousLinearMap.le_opNorm Φ f
        rw [hzero, zero_mul] at hle
        have h0 : ‖Φ f‖ = 0 := le_antisymm hle (norm_nonneg _)
        exact norm_eq_zero.mp h0
      exact hΦ0 hΦeq
    have hcpos : 0 < ‖(Φ : StrongDual 𝕜 (StrongDual 𝕜 E))‖ := hcposCLM
    set c : ℝ := ‖(Φ : StrongDual 𝕜 (StrongDual 𝕜 E))‖ with hcdef
    set Ψ : StrongDual 𝕜 (StrongDual 𝕜 E) :=
      ((c⁻¹ : ℝ) : 𝕜) • (Φ : StrongDual 𝕜 (StrongDual 𝕜 E)) with hΨdef
    have hΦeq : (Φ : StrongDual 𝕜 (StrongDual 𝕜 E)) = (c : 𝕜) • Ψ := by
      have hcc : (c : 𝕜) * ((c⁻¹ : ℝ) : 𝕜) = 1 := by
        rw [← RCLike.ofReal_mul, mul_inv_cancel₀ hcpos.ne', RCLike.ofReal_one]
      rw [hΨdef, smul_smul, hcc, one_smul]
    have hΨnorm : ‖Ψ‖ = 1 := by
      apply le_antisymm
      · have h := ContinuousLinearMap.opNorm_smul_le ((c⁻¹ : ℝ) : 𝕜)
          (Φ : StrongDual 𝕜 (StrongDual 𝕜 E))
        rw [hΨdef]
        calc ‖((c⁻¹ : ℝ) : 𝕜) • (Φ : StrongDual 𝕜 (StrongDual 𝕜 E))‖
            ≤ ‖((c⁻¹ : ℝ) : 𝕜)‖ * ‖(Φ : StrongDual 𝕜 (StrongDual 𝕜 E))‖ := h
          _ = c⁻¹ * c := by
            rw [RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hcpos), ← hcdef]
          _ = 1 := inv_mul_cancel₀ hcpos.ne'
      · have h := ContinuousLinearMap.opNorm_smul_le (c : 𝕜) Ψ
        have hΦ : ‖(Φ : StrongDual 𝕜 (StrongDual 𝕜 E))‖ ≤ ‖(c : 𝕜)‖ * ‖Ψ‖ := by
          rw [hΦeq]
          exact h
        rw [← hcdef, RCLike.norm_ofReal, abs_of_pos hcpos] at hΦ
        have h1 : c * 1 ≤ c * ‖Ψ‖ := by
          rw [mul_one]
          exact hΦ
        exact le_of_mul_le_mul_left h1 hcpos
    obtain ⟨y, hy⟩ := milman_pettis_aux hΨnorm
    refine ⟨(c : 𝕜) • y, fun f => ?_⟩
    rw [hΦeq, smul_apply, hy (f : StrongDual 𝕜 E), map_smul]

end MathlibExt.Analysis.FunctionalAnalysis.MilmanPettisWanted
end

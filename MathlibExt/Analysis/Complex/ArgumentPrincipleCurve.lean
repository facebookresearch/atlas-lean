/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Meromorphic.Divisor
public import MathlibExt.Analysis.Complex.ResidueTheorem
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Topology.Perfect
import MathlibExt.Analysis.Complex.ArgumentPrinciple

/-!
# The argument principle for a simple closed curve

Let `f` be meromorphic on an open set `Ω`, and let `γ` be a positively oriented simple closed
piecewise `C¹` curve in `Ω` whose inside lies in `Ω` and which passes through no zero and no pole
of `f`. Then `(2πi)⁻¹ ∫_γ f'(z) / f(z) dz = N - P`, where `N` and `P` are the numbers of zeros and
of poles of `f` inside `γ`, counted with multiplicity (`MeromorphicOn.argument_principle`).

The curve integral is Mathlib's `curveIntegral` of `logDeriv f z • ContinuousLinearMap.id ℂ ℂ`,
and `f'/f` is `logDeriv f`. `N` and `P` are the sums over the inside of `γ` of the positive and
negative parts of Mathlib's divisor `MeromorphicOn.divisor f Ω`; both sums are finite. The inside
of `γ` is `Set.inside (range γ)` and positive orientation is the hypothesis that the winding number
`Complex.windingNumber γ w` is `1` for `w` inside `γ`, as in the residue theorem
(`Complex.two_pi_I_inv_mul_curveIntegral_eq_finsum_residue`).

The proof applies the residue theorem to `g'/g`, where `g` is the normal form of `f` on `Ω`
(`toMeromorphicNFOn f Ω`). Mathlib's meromorphic functions may take arbitrary values on a discrete
set; the normal form repairs them without changing the divisor, so `g'/g` is holomorphic off the
zeros and poles. On `γ`, `f'/f` and `g'/g` differ at finitely many points, and at almost every
parameter where `γ` passes through one of them the derivative of `γ` vanishes, so the two curve
integrals agree. The residue of `g'/g` at a zero or pole is its order, by the argument principle
on a small disc,
`MathlibExt.Analysis.Complex.ArgumentPrinciple.argumentPrinciple_closedBall_general`.

Rubric-guided revision of v1 ComplexVariables target 22 (`argument_principle` in
`v1/Atlas/ComplexVariables/code/Lecture14.lean` at commit
`6191bf1ba03d204784385ef5be2472be88035b93`). Archived defects fixed:
* the curve was a circle `C(c, R)`; it is now any closed piecewise `C¹` path with its inside;
* the zeros, poles, multiplicities, radii and local factors were data supplied by the user, with
  redundant hypotheses; `N` and `P` are now read off the divisor of `f`, and their finiteness is
  proved;
* `f` was never assumed meromorphic, only `f'/f` was constrained; `f` is now meromorphic on `Ω`
  and the boundary condition is the source's "no zeros nor poles on `γ`";
* the proof depended on the false `sorry`ed lemmas `diffContOnCl_piecewise_cauchy_extension` and
  `continuousOn_deriv_of_differentiableAt_closedBall`; it now goes through Cauchy's theorem for
  cycles and the residue theorem, with no `sorry`.

The archived formalization and its original license/provenance remain in `v1/` (the original
license text is `v1/LICENSE`).
-/

set_option autoImplicit false

open Filter MeasureTheory Metric Set Topology
open scoped Real

namespace Complex

/-- A curve integral does not see the values of the integrand on a finite set: at almost every
parameter where the path takes a value in the set, its derivative vanishes. -/
private theorem curveIntegral_congr_of_finite {x : ℂ} {γ : Path x x} {φ ψ : ℂ → ℂ} {P : Set ℂ}
    (hP : P.Finite) (h : ∀ z ∈ range γ, z ∉ P → φ z = ψ z) :
    ∫ᶜ z in γ, φ z • ContinuousLinearMap.id ℂ ℂ = ∫ᶜ z in γ, ψ z • ContinuousLinearMap.id ℂ ℂ := by
  simp only [curveIntegral_eq_intervalIntegral_deriv, smul_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul]
  -- The parameters mapped into `P` are a countable set and a perfect set.
  obtain ⟨V, D, hV, hD, hA⟩ :=
    exists_countable_union_perfect_of_isClosed (hP.isClosed.preimage γ.continuous_extend)
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hV.measure_zero volume)] with t htV _
  by_cases ht : γ.extend t ∈ P
  · have htD : t ∈ D := ((hA ▸ ht : t ∈ V ∪ D)).resolve_left htV
    have h0 : deriv γ.extend t = 0 :=
      deriv_zero_of_frequently_mem P (fun h => Set.Infinite.of_accPt h hP)
        ((accPt_iff_frequently_nhdsNE.1 (hD.acc t htD)).mono fun s hs =>
          (hA.symm ▸ Or.inr hs : s ∈ γ.extend ⁻¹' P))
    rw [h0, mul_zero, mul_zero]
  · rw [h _ (γ.extend_range ▸ mem_range_self t) ht]

/-- If `g` is meromorphic in normal form at `z` with zero divisor there (order `0` or `⊤`), then
`g'/g` is holomorphic at `z`. -/
private theorem differentiableAt_logDeriv {g : ℂ → ℂ} {z : ℂ} (hg : MeromorphicNFAt g z)
    (h : (meromorphicOrderAt g z).untop₀ = 0) : DifferentiableAt ℂ (logDeriv g) z := by
  rcases WithTop.untop₀_eq_zero.1 h with h0 | htop
  · have han : AnalyticAt ℂ g z := hg.meromorphicOrderAt_nonneg_iff_analyticAt.1 h0.ge
    exact (han.deriv.div han (hg.meromorphicOrderAt_eq_zero_iff.1 h0)).differentiableAt
  · -- `g` vanishes near `z`, hence so does `g'/g`.
    have han : AnalyticAt ℂ g z :=
      hg.meromorphicOrderAt_nonneg_iff_analyticAt.1 (htop ▸ le_top)
    have hzero : g =ᶠ[𝓝 z] 0 :=
      analyticOrderAt_eq_top.1 (by simpa [han.meromorphicOrderAt_eq] using htop)
    have hlog : logDeriv g =ᶠ[𝓝 z] 0 := hzero.eventuallyEq_nhds.mono fun w hw => by
      rw [logDeriv_apply, hw.deriv_eq, hw.eq_of_nhds]
      simp
    exact (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq hlog

/-- Let `g` be meromorphic in normal form on a closed disc about `a`, of finite order at `a` and
with zero divisor at every other point of the disc. Then the residue of `g'/g` at `a` is the
order of `g` at `a`. -/
private theorem residue_logDeriv {Ω : Set ℂ} {g : ℂ → ℂ} (hg : MeromorphicNFOn g Ω) {a : ℂ}
    {r : ℝ} (hr : 0 < r) (hrΩ : closedBall a r ⊆ Ω)
    (hiso : ∀ w ∈ closedBall a r, w ≠ a → (meromorphicOrderAt g w).untop₀ = 0)
    (ha : meromorphicOrderAt g a ≠ ⊤) :
    residue (logDeriv g) a = (meromorphicOrderAt g a).untop₀ := by
  have hgB : MeromorphicOn g (closedBall a r) := hg.meromorphicOn.mono_set hrΩ
  have htop : ∀ z ∈ closedBall a r, meromorphicOrderAt g z ≠ ⊤ := fun z hz =>
    hgB.meromorphicOrderAt_ne_top_of_isPreconnected (convex_closedBall a r).isPreconnected
      (mem_closedBall_self hr.le) hz ha
  have hbd : ∀ z ∈ sphere a r, MeromorphicOn.divisor g (closedBall a r) z = 0 := fun z hz => by
    rw [MeromorphicOn.divisor_apply hgB (sphere_subset_closedBall hz)]
    exact hiso z (sphere_subset_closedBall hz) (ne_of_mem_sphere hz hr.ne')
  have hsum : ∑ᶠ z, MeromorphicOn.divisor g (ball a r) z = (meromorphicOrderAt g a).untop₀ := by
    have hgb : MeromorphicOn g (ball a r) := hgB.mono_set ball_subset_closedBall
    rw [finsum_eq_single _ a fun z hz => ?_, MeromorphicOn.divisor_apply hgb (mem_ball_self hr)]
    by_cases hzB : z ∈ ball a r
    · rw [MeromorphicOn.divisor_apply hgb hzB]
      exact hiso z (ball_subset_closedBall hzB) hz
    · exact (MeromorphicOn.divisor g (ball a r)).apply_eq_zero_of_notMem hzB
  rw [residue_eq_circleIntegral (Ω := closedBall a r) (fun w hw =>
      (differentiableAt_logDeriv (hg (hrΩ hw.1)) (hiso w hw.1 hw.2)).differentiableWithinAt) hr
      subset_rfl,
    MathlibExt.Analysis.Complex.ArgumentPrinciple.argumentPrinciple_closedBall_general hr hgB htop
      hbd, hsum, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ two_pi_I_ne_zero, one_mul]

end Complex

namespace MeromorphicOn

/-- **Argument principle** for a simple closed curve. Let `f` be meromorphic on an open set `Ω`,
and let `γ` be a positively oriented simple closed piecewise `C¹` curve in `Ω` whose inside lies
in `Ω` and which passes through no zero or pole of `f`. Then `f` has finitely many zeros and poles
inside `γ`, and `(2πi)⁻¹ ∫_γ f'(z) / f(z) dz = N - P`, where `N` and `P` are the numbers of zeros
and of poles of `f` inside `γ`, counted with multiplicity: the sums of the positive and negative
parts of the divisor of `f` over the inside of `γ`.

Positive orientation, implicit in the source, is the hypothesis that the winding number
`n(γ, w)` is `1` for every `w` inside `γ`, the same encoding as in the residue theorem
(`Complex.two_pi_I_inv_mul_curveIntegral_eq_finsum_residue`). For `f z = z - w` with `w` inside
`γ` the conclusion is this hypothesis at `w`; for other `f` it is the residue theorem applied to
`f'/f`. For a simple closed curve the Jordan curve theorem gives `n(γ, w) = ±1` inside, and the
orientation fixes the sign; with orientation stated this way the proof does not use simplicity,
which is kept because the source states it. -/
public theorem argument_principle {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → ℂ}
    (hf : MeromorphicOn f Ω) {x : ℂ} {γ : Path x x} (hγ : γ.IsPiecewiseC1)
    (_hγ_simple : InjOn γ (Iio 1))
    (hγ_pos : ∀ w ∈ (range γ).inside, Complex.windingNumber γ w = 1) (hγΩ : range γ ⊆ Ω)
    (hinsΩ : (range γ).inside ⊆ Ω) (hγf : ∀ z ∈ range γ, meromorphicOrderAt f z = 0) :
    ((divisor f Ω).support ∩ (range γ).inside).Finite ∧
      (2 * π * Complex.I)⁻¹ * ∫ᶜ z in γ, logDeriv f z • ContinuousLinearMap.id ℂ ℂ =
        (((∑ᶠ z ∈ (range γ).inside, (divisor f Ω)⁺ z) -
          ∑ᶠ z ∈ (range γ).inside, (divisor f Ω)⁻ z : ℤ) : ℂ) := by
  set g := toMeromorphicNFOn f Ω
  have hg : MeromorphicNFOn g Ω := meromorphicNFOn_toMeromorphicNFOn f Ω
  set D := divisor f Ω
  have hDg : ∀ z ∈ Ω, D z = (meromorphicOrderAt g z).untop₀ := fun z hz => by
    rw [divisor_apply hf hz, meromorphicOrderAt_toMeromorphicNFOn hf hz]
  -- The zeros and poles of `f` do not accumulate in `Ω` and do not lie on `γ`.
  have hS : ∀ z ∈ Ω, ∀ᶠ w in 𝓝[≠] z, w ∉ D.support := by
    intro z hz
    filter_upwards [mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 D.eq_zero_codiscreteWithin z hz,
      nhdsWithin_le_nhds (hΩ.mem_nhds hz)] with w hw hwΩ
    rcases hw with hw | hw
    · exact Function.notMem_support.2 hw
    · exact absurd hwΩ hw
  have hSγ : ∀ a ∈ D.support, a ∉ range γ := fun a ha haγ => ha (by
    rw [divisor_apply hf (hγΩ haγ), hγf a haγ, WithTop.untop₀_zero])
  -- `g'/g` is holomorphic off the zeros and poles, so the residue theorem applies to it.
  have hdiff : DifferentiableOn ℂ (logDeriv g) (Ω \ D.support) := fun z hz =>
    (Complex.differentiableAt_logDeriv (hg hz.1)
      (by rw [← hDg z hz.1]; exact Function.notMem_support.1 hz.2)).differentiableWithinAt
  obtain ⟨hfin, hres⟩ :=
    Complex.two_pi_I_inv_mul_curveIntegral_eq_finsum_residue_of_windingNumber_eq_one hΩ hS hdiff
      hγ hγ_pos hγΩ hinsΩ hSγ
  refine ⟨hfin, ?_⟩
  -- On `γ`, `f'/f` and `g'/g` differ only at the finitely many points where `f ≠ g`.
  have hγint : ∫ᶜ z in γ, logDeriv f z • ContinuousLinearMap.id ℂ ℂ =
      ∫ᶜ z in γ, logDeriv g z • ContinuousLinearMap.id ℂ ℂ := by
    have hP : (range γ \ {z | f z = g z}).Finite :=
      (isCompact_range γ.continuous).finite_sdiff_of_mem_codiscreteWithin
        (codiscreteWithin_mono hγΩ (toMeromorphicNFOn_eqOn_codiscrete hf))
    refine Complex.curveIntegral_congr_of_finite hP fun z hz hzP => ?_
    have hfg : f z = g z := by_contra fun h => hzP ⟨hz, h⟩
    have hev : f =ᶠ[𝓝 z] g := eventuallyEq_nhds_of_eventuallyEq_nhdsNE
      (hf.toMeromorphicNFOn_eq_self_on_nhdsNE (hγΩ hz)).symm hfg
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hfg]
  -- The residue of `g'/g` at a zero or pole is the order there, which is the divisor of `f`.
  have hresD : ∀ a ∈ D.support, Complex.residue (logDeriv g) a = D a := by
    intro a ha
    have haΩ : a ∈ Ω := D.supportWithinDomain ha
    have h1 := hS a haΩ
    rw [eventually_nhdsWithin_iff] at h1
    obtain ⟨r, hr, hrU⟩ := nhds_basis_closedBall.mem_iff.1 (inter_mem (hΩ.mem_nhds haΩ) h1)
    rw [hDg a haΩ]
    refine Complex.residue_logDeriv hg hr (fun w hw => (hrU hw).1) (fun w hw hwa => ?_) ?_
    · rw [← hDg w (hrU hw).1]
      exact Function.notMem_support.1 ((hrU hw).2 hwa)
    · intro htop
      exact ha (by rw [hDg a haΩ, htop, WithTop.untop₀_top])
  -- Sums over the inside reduce to sums over the finitely many zeros and poles inside `γ`.
  have hsum : ∀ φ : ℤ → ℤ, φ 0 = 0 →
      ∑ᶠ z ∈ (range γ).inside, φ (D z) = ∑ z ∈ hfin.toFinset, φ (D z) := by
    intro φ hφ
    rw [← finsum_mem_eq_finite_toFinset_sum _ hfin]
    refine finsum_mem_inter_support_eq _ _ _ ?_
    ext z
    simp only [mem_inter_iff, Function.mem_support]
    exact ⟨fun h => ⟨⟨fun hz => h.2 (by rw [hz, hφ]), h.1⟩, h.2⟩, fun h => ⟨h.1.2, h.2⟩⟩
  rw [hγint, hres, finsum_mem_eq_finite_toFinset_sum _ hfin,
    Finset.sum_congr rfl fun a ha => hresD a (hfin.mem_toFinset.1 ha).1]
  simp only [Function.locallyFinsuppWithin.posPart_apply,
    Function.locallyFinsuppWithin.negPart_apply]
  rw [hsum (·⁺) posPart_zero, hsum (·⁻) negPart_zero, ← Finset.sum_sub_distrib]
  push_cast
  refine Finset.sum_congr rfl fun z _ => ?_
  exact_mod_cast (posPart_sub_negPart (D z)).symm

end MeromorphicOn

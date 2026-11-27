/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Weak maximum principle for the Laplacian

On a bounded open set `U` of a finite-dimensional real inner product space, a function that is
`C²` on `U`, continuous on `closure U` and subharmonic (`0 ≤ Δ u`) attains its maximum over
`closure U` at a point of the boundary `frontier U`. For harmonic functions (Mathlib's
`InnerProductSpace.HarmonicOnNhd`) both the maximum and the minimum are attained on the boundary,
and the Dirichlet problem for Poisson's equation `-Δ u = f` has at most one solution in
`C²(U) ∩ C(closure U)`.

The proof is the perturbation argument: `u + ε ‖x‖²` has Laplacian `Δ u + 2 ε n > 0`, so it has no
interior maximum, because the Laplacian of a `C²` function at an interior local maximum is
nonpositive. That last fact is proved from the second-order necessary condition along lines,
`D²f(z)(e, e) = φ''(0)` for `φ(t) = f(z + t e)` (Evans, Math 170 notes, Theorem 1.1.2 and its
proof), and the formula of Mathlib's Laplacian in an orthonormal basis.

## Main results

* `laplacian_nonpos_of_isLocalMax`: `Δ f z ≤ 0` at an interior local maximum of a `C²` function.
* `exists_mem_frontier_isMaxOn_of_laplacian_nonneg`: weak maximum principle for subharmonic
  functions.
* `exists_mem_frontier_isMaxOn_of_harmonicOnNhd`, `exists_mem_frontier_isMinOn_of_harmonicOnNhd`:
  weak maximum and minimum principles for harmonic functions.
* `eqOn_closure_of_neg_laplacian_eq`: uniqueness for the Dirichlet problem for `-Δ u = f`.

The space is assumed nontrivial: in dimension `0` the only nonempty open set is the whole
(one-point) space, which is bounded with empty boundary, and every function is harmonic.

## References

* L. C. Evans, *Mathematics 170: Mathematical Methods for Optimization, Finite Dimensional
  Optimization*, lecture notes, Spring 2021 version, https://math.berkeley.edu/~evans/, §1.1.2,
  Theorem 1.1.2 and Remark (ii).
* L. C. Evans, *Entropy and Partial Differential Equations*, lecture notes,
  https://math.berkeley.edu/~evans/entropy.and.PDE.pdf, Chapter IV.A.3: Harnack's inequality, the
  strong maximum principle (Corollary) and
  the weak maximum principle obtained in its proof, for `-∑ (a^{ij} u_{x_i})_{x_j} = 0`.
* M. Schmidt, *Partial Differential Equations*, lecture notes, Universität Mannheim, HWS 2025,
  Chapter 3 (Laplace equation),
  https://www.wim.uni-mannheim.de/media/Lehrstuehle/wim/schmidt/HWS2025/chapter_3.pdf: Weak Maximum
  Principle 3.11 and Theorem 3.13 (maximum principle for elliptic
  `L u ≥ 0`, proved by the same perturbation argument with `exp(α x₁)`).
* L. C. Evans, *Partial Differential Equations*, 2nd ed., AMS Graduate Studies in Mathematics 19
  (2010), Chapter 2 (properties of harmonic functions: maximum principle and uniqueness). The book
  was not available to this formalization; theorem numbers are not cited from it.
-/

@[expose] public section

open InnerProductSpace Filter Topology Set Laplacian

namespace MathlibExt.Analysis.PDE.LaplaceMaximumPrinciple

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Second derivative along a line.** If `f : E → ℝ` is `C²` at `z`, then the second
derivative `D²f(z)(e, e)` equals `φ''(0)` for `φ(t) = f(z + t e)`. This is the chain-rule
computation in the proof of Theorem 1.1.2 of L. C. Evans, *Math 170 lecture notes* (Spring 2021),
§1.1.2, stated for Mathlib's `iteratedFDeriv`. -/
theorem iteratedFDeriv_two_apply_eq_deriv_deriv {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z)
    (e : E) :
    iteratedFDeriv ℝ 2 f z ![e, e] = deriv (deriv fun t : ℝ => f (z + t • e)) 0 := by
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hℓ : ∀ t : ℝ, HasDerivAt (fun t : ℝ => z + t • e) e t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const e).const_add z
  have hcont : Tendsto (fun t : ℝ => z + t • e) (𝓝 0) (𝓝 z) := by
    have : Continuous fun t : ℝ => z + t • e := by fun_prop
    simpa using this.tendsto 0
  have hdiff : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ f (z + t • e) :=
    hcont.eventually ((hf.eventually (by simp)).mono fun y hy =>
      hy.differentiableAt (by simp))
  have hderiv : deriv (fun t : ℝ => f (z + t • e)) =ᶠ[𝓝 0]
      fun t => fderiv ℝ f (z + t • e) e := by
    filter_upwards [hdiff] with t ht
    exact ((ht.hasFDerivAt).comp_hasDerivAt t (hℓ t)).deriv
  rw [hderiv.deriv_eq]
  have hd2 : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have hd2' : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) z) (z + (0 : ℝ) • e) := by
    simpa using hd2.hasFDerivAt
  have h := ((ContinuousLinearMap.apply ℝ ℝ e).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hd2'.comp_hasDerivAt (0 : ℝ) (hℓ 0)))
  rw [show (fun t : ℝ => fderiv ℝ f (z + t • e) e) =
    ⇑(ContinuousLinearMap.apply ℝ ℝ e) ∘ fderiv ℝ f ∘ fun t : ℝ => z + t • e from rfl, h.deriv]
  simp

/-- **Nonpositive second derivatives at a local maximum.** If `f : E → ℝ` is `C²` at a local
maximum `z`, then `D²f(z)(e, e) ≤ 0` for every direction `e`: the second-order necessary condition,
the maximum version of Theorem 1.1.2 and Remark (ii) of L. C. Evans, *Math 170 lecture notes*
(Spring 2021), §1.1.2 (stated there for minimizers, with `∇²f(x₀) ≽ 0`). -/
theorem iteratedFDeriv_two_nonpos_of_isLocalMax {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z)
    (hmax : IsLocalMax f z) (e : E) : iteratedFDeriv ℝ 2 f z ![e, e] ≤ 0 := by
  rw [iteratedFDeriv_two_apply_eq_deriv_deriv hf e]
  set g : ℝ → ℝ := fun t => f (z + t • e) with hg_def
  have hgc : ContinuousAt g 0 := by
    have : ContinuousAt (fun t : ℝ => z + t • e) 0 := by fun_prop
    exact ContinuousAt.comp_of_eq hf.continuousAt this (by simp)
  have hgmax : IsLocalMax g 0 := by
    have : ContinuousAt (fun t : ℝ => z + t • e) 0 := by fun_prop
    exact IsLocalMax.comp_continuous (g := fun t : ℝ => z + t • e) (b := 0)
      (by simpa using hmax) this
  by_contra hpos
  push Not at hpos
  have hgmin : IsLocalMin g 0 :=
    isLocalMin_of_deriv_deriv_pos hpos hgmax.deriv_eq_zero hgc
  have hconst : g =ᶠ[𝓝 0] fun _ => g 0 := by
    filter_upwards [hgmax, hgmin] with t h1 h2
    exact le_antisymm h1 h2
  rw [hconst.deriv.deriv_eq] at hpos
  simp at hpos

variable [FiniteDimensional ℝ E]

/-- **The Laplacian is nonpositive at an interior maximum.** In a finite-dimensional real inner
product space, if `f` is `C²` at a local maximum `z`, then `Δ f z ≤ 0`: the trace of the
nonpositive second derivative (L. C. Evans, *Math 170 lecture notes*, Spring 2021, Theorem 1.1.2
and Remark (ii), applied to `-f`). This is the step behind the weak maximum principle. -/
theorem laplacian_nonpos_of_isLocalMax {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z)
    (hmax : IsLocalMax f z) : Δ f z ≤ 0 := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  exact Finset.sum_nonpos fun i _ => iteratedFDeriv_two_nonpos_of_isLocalMax hf hmax _

/-- **Laplacian of the squared norm.** In a finite-dimensional real inner product space of
dimension `n`, `Δ ‖x‖² = 2 n` at every point: the perturbation used in the classical proof of the
weak maximum principle (the Laplacian of `|x|² = ∑ x_i²` in `ℝⁿ`). -/
theorem laplacian_norm_sq (z : E) :
    Δ (fun x : E => ‖x‖ ^ 2) z = 2 * Module.finrank ℝ E := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  have key : ∀ e : E, iteratedFDeriv ℝ 2 (fun x : E => ‖x‖ ^ 2) z ![e, e] = 2 * ‖e‖ ^ 2 := by
    intro e
    rw [iteratedFDeriv_two_apply_eq_deriv_deriv (contDiff_norm_sq ℝ).contDiffAt e]
    have h1 : (fun t : ℝ => ‖z + t • e‖ ^ 2) =
        fun t => ‖z‖ ^ 2 + 2 * inner ℝ z e * t + ‖e‖ ^ 2 * t ^ 2 := by
      funext t
      rw [norm_add_sq_real, norm_smul, inner_smul_right, Real.norm_eq_abs, mul_pow, sq_abs]
      ring
    have h2 : deriv (fun t : ℝ => ‖z‖ ^ 2 + 2 * inner ℝ z e * t + ‖e‖ ^ 2 * t ^ 2) =
        fun t => 2 * inner ℝ z e + ‖e‖ ^ 2 * (2 * t) := by
      funext t
      have := (((hasDerivAt_id t).const_mul (2 * inner ℝ z e)).const_add (‖z‖ ^ 2)).add
        (((hasDerivAt_id t).pow 2).const_mul (‖e‖ ^ 2))
      have h3 : HasDerivAt (fun t : ℝ => ‖z‖ ^ 2 + 2 * inner ℝ z e * t + ‖e‖ ^ 2 * t ^ 2)
          (2 * inner ℝ z e + ‖e‖ ^ 2 * (2 * t)) t := by
        convert this using 1
        · funext x; simp [add_assoc]
        · simp
      exact h3.deriv
    rw [h1, h2]
    have := (((hasDerivAt_id (0 : ℝ)).const_mul 2).const_mul (‖e‖ ^ 2)).const_add
      (2 * inner ℝ z e)
    rw [show (fun t : ℝ => 2 * inner ℝ z e + ‖e‖ ^ 2 * (2 * t)) =
      fun t => 2 * inner ℝ z e + ‖e‖ ^ 2 * (2 * id t) from rfl, this.deriv]
    ring
  simp only [key, OrthonormalBasis.norm_eq_one, one_pow, mul_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **Weak maximum principle for subharmonic functions.** Let `U` be a nonempty bounded open
subset of a nontrivial finite-dimensional real inner product space. If `u` is continuous on
`closure U`, `C²` at every point of `U` and `0 ≤ Δ u` on `U`, then `u` attains its maximum over
`closure U` at a point of `frontier U`, that is `max_{closure U} u = max_{∂U} u`.

This is Theorem 3.13 of M. Schmidt, *Partial Differential Equations*, lecture notes, Universität
Mannheim (HWS 2025), Chapter 3, for the operator `L = Δ` (there `L u ≥ 0` for a general elliptic
`L` with coefficients continuous up to the boundary), with the same perturbation proof, here by
`ε ‖x‖²`. The weak maximum principle for harmonic functions (Evans, *Partial Differential
Equations*, 2nd ed., Chapter 2) is the case `Δ u = 0`; L. C. Evans, *Entropy and Partial
Differential Equations*, lecture notes, Chapter IV.A.3, proves it for
`-∑ (a^{ij} u_{x_i})_{x_j} = 0` and `u ∈ C²(closure U)` by testing against `u⁻`. -/
theorem exists_mem_frontier_isMaxOn_of_laplacian_nonneg [Nontrivial E] {U : Set E} {u : E → ℝ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hne : U.Nonempty)
    (hc : ContinuousOn u (closure U)) (hd : ∀ x ∈ U, ContDiffAt ℝ 2 u x)
    (hΔ : ∀ x ∈ U, 0 ≤ Δ u x) :
    ∃ y ∈ frontier U, IsMaxOn u (closure U) y := by
  have hK : IsCompact (frontier U) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_frontier
      (hUb.closure.subset frontier_subset_closure)
  have hKne : (frontier U).Nonempty := by
    refine nonempty_frontier_iff.mpr ⟨hne, fun h => ?_⟩
    exact NormedSpace.unbounded_univ ℝ E (h ▸ hUb)
  obtain ⟨y, hy, hymax⟩ := hK.exists_isMaxOn hKne (hc.mono frontier_subset_closure)
  refine ⟨y, hy, fun x₀ hx₀ => ?_⟩
  simp only [mem_ofPred_eq]
  by_contra hlt
  push Not at hlt
  have hcl : IsCompact (closure U) := hUb.isCompact_closure
  obtain ⟨R, hR⟩ := hUb.closure.exists_norm_le
  set δ := u x₀ - u y with hδ
  have hδpos : 0 < δ := by linarith
  set ε := δ / (2 * (R ^ 2 + 1)) with hε
  have hεpos : 0 < ε := by positivity
  set v : E → ℝ := u + ε • fun x : E => ‖x‖ ^ 2 with hv
  have hvc : ContinuousOn v (closure U) :=
    hc.add (continuousOn_const.smul (by fun_prop))
  obtain ⟨z, hz, hzmax⟩ := hcl.exists_isMaxOn ⟨x₀, hx₀⟩ hvc
  -- `v` exceeds its boundary values at `x₀`, so `z` is interior.
  have hεR : ε * R ^ 2 < δ := by
    rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [sq_nonneg R]
  have hzU : z ∈ U := by
    by_contra hzU
    have hzf : z ∈ frontier U := by
      rw [frontier, hU.interior_eq]
      exact ⟨hz, hzU⟩
    have h1 : v x₀ ≤ v z := hzmax hx₀
    have h2 : u z ≤ u y := hymax hzf
    have h3 : ‖z‖ ≤ R := hR z hz
    have h4 : ‖z‖ ^ 2 ≤ R ^ 2 := by
      have := norm_nonneg z
      nlinarith
    simp only [hv, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1
    nlinarith [sq_nonneg ‖x₀‖, mul_le_mul_of_nonneg_left h4 hεpos.le]
  have hloc : IsLocalMax v z :=
    hzmax.isLocalMax (mem_of_superset (hU.mem_nhds hzU) subset_closure)
  have hsq : ContDiffAt ℝ 2 (fun x : E => ‖x‖ ^ 2) z := (contDiff_norm_sq ℝ).contDiffAt
  have hsq' : ContDiffAt ℝ 2 (ε • fun x : E => ‖x‖ ^ 2) z := hsq.const_smul ε
  have hvd : ContDiffAt ℝ 2 v z := (hd z hzU).add hsq'
  have hneg := laplacian_nonpos_of_isLocalMax hvd hloc
  rw [hv, (hd z hzU).laplacian_add hsq', laplacian_smul ε hsq,
    laplacian_norm_sq] at hneg
  have hn : (0 : ℝ) < Module.finrank ℝ E := by exact_mod_cast Module.finrank_pos
  have := hΔ z hzU
  simp only [smul_eq_mul] at hneg
  nlinarith [mul_pos hεpos hn]

/-- **Weak maximum principle for harmonic functions.** Let `U` be a nonempty bounded open subset
of a nontrivial finite-dimensional real inner product space, and let `u` be harmonic on `U`
(Mathlib's `HarmonicOnNhd`) and continuous on `closure U`. Then `u` attains its maximum over
`closure U` on `frontier U`: Weak Maximum Principle 3.11 of M. Schmidt, *Partial Differential
Equations*, lecture notes, Universität Mannheim (HWS 2025), Chapter 3, which deduces it from the
strong principle; here it is proved directly. This is the weak form only; the strong form (an
interior maximum
on a connected `U` forces `u` to be constant) is the Corollary of Chapter IV.A.3 in L. C. Evans,
*Entropy and Partial Differential Equations*, lecture notes, and is recorded as wanted. -/
theorem exists_mem_frontier_isMaxOn_of_harmonicOnNhd [Nontrivial E] {U : Set E} {u : E → ℝ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hne : U.Nonempty)
    (hc : ContinuousOn u (closure U)) (hu : HarmonicOnNhd u U) :
    ∃ y ∈ frontier U, IsMaxOn u (closure U) y :=
  exists_mem_frontier_isMaxOn_of_laplacian_nonneg hU hUb hne hc (fun x hx => (hu x hx).1)
    (fun x hx => ((hu x hx).2.self_of_nhds).symm ▸ le_rfl)

/-- **Weak minimum principle for harmonic functions.** Under the hypotheses of the weak maximum
principle, a harmonic `u` also attains its minimum over `closure U` on `frontier U` (apply the
maximum principle to `-u`; Evans, *Partial Differential Equations*, 2nd ed., Chapter 2). -/
theorem exists_mem_frontier_isMinOn_of_harmonicOnNhd [Nontrivial E] {U : Set E} {u : E → ℝ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hne : U.Nonempty)
    (hc : ContinuousOn u (closure U)) (hu : HarmonicOnNhd u U) :
    ∃ y ∈ frontier U, IsMinOn u (closure U) y := by
  obtain ⟨y, hy, hmax⟩ := exists_mem_frontier_isMaxOn_of_harmonicOnNhd hU hUb hne hc.neg hu.neg
  exact ⟨y, hy, fun x hx => by simpa using hmax hx⟩

/-- **Uniqueness for the Dirichlet problem for Poisson's equation.** Let `U` be a bounded open
subset of a nontrivial finite-dimensional real inner product space. If `u₁, u₂` are continuous on
`closure U`, `C²` on `U`, solve `-Δ u = f` on `U` and agree on `frontier U`, then they agree on
`closure U`. No regularity of `f` is needed. This is the uniqueness theorem for the Dirichlet
problem for Poisson's equation (Evans, *Partial Differential Equations*, 2nd ed., Chapter 2;
M. Schmidt, *Partial Differential Equations*, lecture notes, Universität Mannheim, HWS 2025,
Chapter 3, §3.3), proved from the weak maximum and minimum principles. -/
theorem eqOn_closure_of_neg_laplacian_eq [Nontrivial E] {U : Set E} {u₁ u₂ f : E → ℝ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hc₁ : ContinuousOn u₁ (closure U)) (hc₂ : ContinuousOn u₂ (closure U))
    (hd₁ : ∀ x ∈ U, ContDiffAt ℝ 2 u₁ x) (hd₂ : ∀ x ∈ U, ContDiffAt ℝ 2 u₂ x)
    (h₁ : ∀ x ∈ U, -Δ u₁ x = f x) (h₂ : ∀ x ∈ U, -Δ u₂ x = f x)
    (hb : EqOn u₁ u₂ (frontier U)) : EqOn u₁ u₂ (closure U) := by
  rcases U.eq_empty_or_nonempty with rfl | hne
  · simp
  have hw : HarmonicOnNhd (u₁ - u₂) U := by
    intro x hx
    refine ⟨(hd₁ x hx).sub (hd₂ x hx), ?_⟩
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [Pi.zero_apply, (hd₁ y hy).laplacian_sub (hd₂ y hy)]
    linarith [h₁ y hy, h₂ y hy]
  obtain ⟨y, hy, hmax⟩ := exists_mem_frontier_isMaxOn_of_harmonicOnNhd hU hUb hne
    (hc₁.sub hc₂) hw
  obtain ⟨y', hy', hmin⟩ := exists_mem_frontier_isMinOn_of_harmonicOnNhd hU hUb hne
    (hc₁.sub hc₂) hw
  intro x hx
  have a := hmax hx
  have b := hmin hx
  simp only [mem_ofPred_eq, Pi.sub_apply] at a b
  linarith [hb hy, hb hy']

end MathlibExt.Analysis.PDE.LaplaceMaximumPrinciple

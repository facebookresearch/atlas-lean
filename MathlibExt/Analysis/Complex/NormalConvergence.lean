/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Calculus.UniformLimitsDeriv

public import MathlibExt.Analysis.Normed.Series.NormalConvergence
public import Mathlib.Analysis.Complex.LocallyUniformLimit

import Mathlib.Analysis.Complex.Liouville
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Normal convergence of complex derivative series

This file proves the Weierstrass M-test for termwise differentiation of locally
normally convergent series of holomorphic functions.
-/

@[expose] public section

open Set Metric Filter Topology ENNReal

/-- **Normal convergence gives summable real sup norms.** Let $E$ be a seminormed additive
commutative group, $S$ a subset of a type $X$ and $f_n \colon X \to E$ for $n \in \mathbb{N}$.
If the series $\sum_n f_n$ converges normally on $S$, that is
$\sum_n \sup_{x \in S} \|f_n(x)\| < \infty$ with the suprema taken in $[0, \infty]$, then the
sequence of sup norms $\left(\sup_{x \in S} \|f_n(x)\|\right)_n$, viewed as real numbers, is
summable. -/
theorem ConvergesNormallyOn.summable_toReal_supNormOn
    {X E : Type*} [SeminormedAddCommGroup E]
    {f : ℕ → X → E} {S : Set X}
    (hf : ConvergesNormallyOn f S) :
    Summable (fun n => (supNormOn (f n) S).toReal) :=
  ENNReal.summable_toReal hf

/-- **Normal convergence implies pointwise absolute convergence.** Let $E$ be a seminormed
additive commutative group, $S$ a subset of a type $X$ and $f_n \colon X \to E$ for
$n \in \mathbb{N}$. If the series $\sum_n f_n$ converges normally on $S$, that is
$\sum_n \sup_{x \in S} \|f_n(x)\| < \infty$ with the suprema taken in $[0, \infty]$, then for
every $x \in S$ the series $\sum_n \|f_n(x)\|$ is summable. -/
theorem ConvergesNormallyOn.summable_norm
    {X E : Type*} [SeminormedAddCommGroup E]
    {f : Nat → X → E} {S : Set X} (hf : ConvergesNormallyOn f S)
    {x : X} (hx : x ∈ S) : Summable (fun n => norm (f n x)) := by
  have hsum := hf.summable_toReal_supNormOn
  exact Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => by
      rw [← ENNReal.ofReal_le_iff_le_toReal (ENNReal.ne_top_of_tsum_ne_top hf n)]
      exact le_iSup (fun y : S => ENNReal.ofReal ‖f n ↑y‖) ⟨x, hx⟩)
    hsum

/-- **Local normal convergence implies pointwise absolute convergence.** Let $E$ be a seminormed
additive commutative group, $S$ a subset of a topological space $X$ and $f_n \colon X \to E$ for
$n \in \mathbb{N}$. If the series $\sum_n f_n$ converges locally normally on $S$, that is every
$x \in S$ has a neighbourhood $U$ with $\sum_n \sup_{y \in U \cap S} \|f_n(y)\| < \infty$ (suprema
taken in $[0, \infty]$), then for every $x \in S$ the series $\sum_n \|f_n(x)\|$ is summable. -/
theorem ConvergesLocallyNormallyOn.summable_norm
    {X E : Type*} [TopologicalSpace X] [SeminormedAddCommGroup E]
    {f : Nat → X → E} {S : Set X} (hf : ConvergesLocallyNormallyOn f S)
    {x : X} (hx : x ∈ S) : Summable (fun n => norm (f n x)) := by
  obtain ⟨U, hU, hnormal⟩ := hf x hx
  have hxU : x ∈ U := mem_of_mem_nhds hU
  exact hnormal.summable_norm ⟨hxU, hx⟩

/-- **Weierstrass M-test: normal convergence implies uniform convergence.** Let $E$ be a complete
normed additive commutative group, $S$ a subset of a type $X$ and $f_n \colon X \to E$ for
$n \in \mathbb{N}$. If the series $\sum_n f_n$ converges normally on $S$, that is
$\sum_n \sup_{x \in S} \|f_n(x)\| < \infty$ with the suprema taken in $[0, \infty]$, then the
partial sums $x \mapsto \sum_{n < N} f_n(x)$ converge uniformly on $S$, as $N \to \infty$, to
the pointwise sum $x \mapsto \sum_{n=0}^{\infty} f_n(x)$. -/
theorem ConvergesNormallyOn.tendstoUniformlyOn_tsum_nat
    {X E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {f : ℕ → X → E} {S : Set X}
    (hf : ConvergesNormallyOn f S) :
    TendstoUniformlyOn (fun N z => ∑ n ∈ Finset.range N, f n z)
      (fun z => ∑' n, f n z) atTop S := by
  have hsum : Summable (fun n => (supNormOn (f n) S).toReal) :=
    hf.summable_toReal_supNormOn
  apply _root_.tendstoUniformlyOn_tsum_nat hsum
  intro n z hz
  have hle : ENNReal.ofReal ‖f n z‖ ≤ supNormOn (f n) S := by
    unfold supNormOn
    exact le_iSup (fun x : S => ENNReal.ofReal ‖f n x‖) ⟨z, hz⟩
  exact (ENNReal.ofReal_le_iff_le_toReal
    (ENNReal.ne_top_of_tsum_ne_top hf n)).mp hle

/-- **Derivative series of a locally normally convergent holomorphic series.** Let $E$ be a
normed space over $\mathbb{C}$, $S \subseteq \mathbb{C}$ an open set and $f_n \colon \mathbb{C}
\to E$ for $n \in \mathbb{N}$ functions that are complex differentiable on $S$. If the series
$\sum_n f_n$ converges locally normally on $S$, that is every $z \in S$ has a neighbourhood $U$
with $\sum_n \sup_{w \in U \cap S} \|f_n(w)\| < \infty$ (suprema taken in $[0, \infty]$), then
the series of derivatives $\sum_n f_n'$ also converges locally normally on $S$. -/
theorem ConvergesLocallyNormallyOn.deriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℕ → ℂ → E} {S : Set ℂ}
    (hf : ConvergesLocallyNormallyOn f S)
    (hS : IsOpen S) (holo : ∀ n, DifferentiableOn ℂ (f n) S) :
    ConvergesLocallyNormallyOn (fun n z => _root_.deriv (f n) z) S := by
  intro z₀ hz₀
  obtain ⟨U, hU, hUnorm⟩ := hf z₀ hz₀
  rcases _root_.mem_nhds_iff.mp hU with ⟨V, hVU, hVopen, hzV⟩
  have hVSopen : IsOpen (V ∩ S) := hVopen.inter hS
  have hzVS : z₀ ∈ V ∩ S := ⟨hzV, hz₀⟩
  obtain ⟨r, hrpos, hball⟩ := Metric.isOpen_iff.mp hVSopen z₀ hzVS
  set s : ℝ := r / 4 with hs
  have hspos : 0 < s := by positivity
  refine ⟨ball z₀ s, ball_mem_nhds z₀ hspos, ?_⟩
  have hCfin : ∀ n, supNormOn (f n) (U ∩ S) ≠ ⊤ :=
    ENNReal.ne_top_of_tsum_ne_top hUnorm
  have hderiv_sup : ∀ n, supNormOn (fun z => _root_.deriv (f n) z) (ball z₀ s)
      ≤ supNormOn (f n) (U ∩ S) / ENNReal.ofReal s := by
    intro n
    apply iSup_le
    rintro ⟨z, hz⟩
    have hcb_sub : closedBall z s ⊆ U ∩ S := by
      intro w hw
      apply Set.inter_subset_inter_left S hVU
      apply hball
      rw [mem_ball]
      calc
        dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
        _ ≤ s + dist z z₀ := by linarith [mem_closedBall.mp hw]
        _ < s + s := by linarith [mem_ball.mp hz]
        _ = r / 2 := by rw [hs]; ring
        _ < r := by linarith
    have hdiff : DiffContOnCl ℂ (f n) (ball z s) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball z (ne_of_gt hspos)]
      exact (holo n).mono (hcb_sub.trans inter_subset_right)
    have hbound : ∀ w ∈ sphere z s,
        ‖f n w‖ ≤ (supNormOn (f n) (U ∩ S)).toReal := by
      intro w hw
      have hwUS : w ∈ U ∩ S := hcb_sub (sphere_subset_closedBall hw)
      apply (ENNReal.ofReal_le_iff_le_toReal (hCfin n)).mp
      unfold supNormOn
      exact le_iSup (fun x : ↥(U ∩ S) => ENNReal.ofReal ‖f n x‖) ⟨w, hwUS⟩
    have hle : ‖_root_.deriv (f n) z‖ ≤ (supNormOn (f n) (U ∩ S)).toReal / s :=
      Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hspos hdiff hbound
    calc
      ENNReal.ofReal ‖_root_.deriv (f n) z‖
          ≤ ENNReal.ofReal ((supNormOn (f n) (U ∩ S)).toReal / s) :=
        ENNReal.ofReal_le_ofReal hle
      _ = supNormOn (f n) (U ∩ S) / ENNReal.ofReal s := by
        rw [ENNReal.ofReal_div_of_pos hspos, ENNReal.ofReal_toReal (hCfin n)]
  have hsum : ∑' n, (supNormOn (f n) (U ∩ S) / ENNReal.ofReal s) ≠ ⊤ := by
    simp_rw [div_eq_mul_inv, ENNReal.tsum_mul_right]
    exact ENNReal.mul_ne_top hUnorm
      (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hspos))
  have hderiv_sup' : ∀ n, supNormOn (fun z => _root_.deriv (f n) z) (ball z₀ s ∩ S)
      ≤ supNormOn (f n) (U ∩ S) / ENNReal.ofReal s :=
    fun n => le_trans (supNormOn_mono Set.inter_subset_left _) (hderiv_sup n)
  exact ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum hderiv_sup')

/-- **Local normal convergence implies locally uniform convergence.** Let $E$ be a complete
normed additive commutative group, $S$ a subset of a topological space $X$ and
$f_n \colon X \to E$ for $n \in \mathbb{N}$. If the series $\sum_n f_n$ converges locally
normally on $S$, that is every $x \in S$ has a neighbourhood $U$ with
$\sum_n \sup_{y \in U \cap S} \|f_n(y)\| < \infty$ (suprema taken in $[0, \infty]$), then the
partial sums $x \mapsto \sum_{n < N} f_n(x)$ converge locally uniformly on $S$, as
$N \to \infty$, to the pointwise sum $x \mapsto \sum_{n=0}^{\infty} f_n(x)$. -/
theorem ConvergesLocallyNormallyOn.tendstoLocallyUniformlyOn_tsum_nat
    {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [CompleteSpace E]
    {f : Nat → X → E} {S : Set X} (hf : ConvergesLocallyNormallyOn f S) :
    TendstoLocallyUniformlyOn
      (fun N x => Finset.sum (Finset.range N) fun n => f n x)
      (fun x => ∑' n, f n x) atTop S := by
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro x hx
  obtain ⟨U, hU, hnormal⟩ := hf x hx
  refine ⟨U ∩ S, ?_, hnormal.tendstoUniformlyOn_tsum_nat⟩
  simpa only [inter_comm] using inter_mem_nhdsWithin S hU

/-- **Termwise differentiation of locally normally convergent holomorphic series.** Let $E$ be a
complete normed space over $\mathbb{C}$, $S \subseteq \mathbb{C}$ an open set and
$f_n \colon \mathbb{C} \to E$ for $n \in \mathbb{N}$ functions that are complex differentiable
on $S$. If the series $\sum_n f_n$ converges locally normally on $S$, that is every $z \in S$
has a neighbourhood $U$ with $\sum_n \sup_{w \in U \cap S} \|f_n(w)\| < \infty$ (suprema taken
in $[0, \infty]$), then for every $z \in S$ the function $w \mapsto \sum_{n=0}^{\infty} f_n(w)$
has derivative $\sum_{n=0}^{\infty} f_n'(z)$ at $z$. -/
theorem ConvergesLocallyNormallyOn.hasDerivAt_tsum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f : Nat → Complex → E} {S : Set Complex} {z : Complex}
    (hf : ConvergesLocallyNormallyOn f S)
    (hS : IsOpen S) (holo : ∀ n, DifferentiableOn Complex (f n) S)
    (hz : z ∈ S) :
    HasDerivAt (fun w => ∑' n, f n w) (∑' n, _root_.deriv (f n) z) z := by
  have hderiv_conv := hf.deriv hS holo
  have hderiv_unif := hderiv_conv.tendstoLocallyUniformlyOn_tsum_nat
  have hderiv_eq : ∀ N w, w ∈ S →
      _root_.deriv (fun z => Finset.sum (Finset.range N) fun k => f k z) w =
        Finset.sum (Finset.range N) fun k => _root_.deriv (f k) w := by
    intro N w hw
    have hfun : (fun z => Finset.sum (Finset.range N) fun k => f k z) =
        Finset.sum (Finset.range N) fun k => f k := by
      ext z
      simp [Finset.sum_apply]
    rw [hfun]
    exact deriv_sum (fun k _ => (holo k w hw).differentiableAt (hS.mem_nhds hw))
  have hderiv_comp : TendstoLocallyUniformlyOn
      (fun N w => _root_.deriv (fun z => Finset.sum (Finset.range N) fun k => f k z) w)
      (fun w => ∑' n, _root_.deriv (f n) w) atTop S :=
    hderiv_unif.congr (fun N w hw => (hderiv_eq N w hw).symm)
  have hpartial_holo : ∀ᶠ N in atTop,
      DifferentiableOn Complex (fun z => Finset.sum (Finset.range N) fun k => f k z) S := by
    apply Filter.Eventually.of_forall
    intro N
    have h1 : (fun z => Finset.sum (Finset.range N) fun k => f k z) =
        Finset.sum (Finset.range N) fun k => f k := by
      ext z
      simp [Finset.sum_apply]
    rw [h1]
    exact DifferentiableOn.sum (fun k _ => holo k)
  have hpointwise : ∀ w ∈ S,
      Tendsto (fun N => Finset.sum (Finset.range N) fun k => f k w) atTop
        (𝓝 (∑' n, f n w)) := by
    intro w hw
    exact (hf.tendstoLocallyUniformlyOn_tsum_nat).tendsto_at hw
  exact hasDerivAt_of_tendsto_locally_uniformly_on' hS hderiv_comp
    hpartial_holo hpointwise hz

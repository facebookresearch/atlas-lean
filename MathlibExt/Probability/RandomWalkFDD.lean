/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Finite-dimensional distributions of the rescaled random walk

Let `R i` be iid with mean `0`, variance `1` and `|R i| ≤ 1`, and let
`f n s = S_{⌊ns⌋} / √n + (ns - ⌊ns⌋) R_{⌊ns⌋} / √n` be the piecewise linear interpolation of the
random walk `S_k = ∑_{i < k} R i`, with time step `1 / n` and space step `1 / √n`. For times
`0 ≤ t 0 < ⋯ < t m`, the increments `f n (t (j + 1)) - f n (t j)` converge jointly in
distribution to independent `𝓝(0, t (j + 1) - t j)` variables
(`ProbabilityTheory.tendstoInDistribution_randomWalk_increments`): the finite-dimensional
distributions of `f n` converge to those of Brownian motion.

Each grid increment `(S_{⌊n t (j+1)⌋} - S_{⌊n t j⌋}) / √n` is a block sum of
`⌊n t (j+1)⌋ - ⌊n t j⌋ ≈ n (t (j+1) - t j)` terms. A central limit theorem for such blocks
(`variable_block_CLT_tendstoInDistribution`, proved from Mathlib's characteristic-function
expansion `taylor_charFun_two`) gives each marginal; disjoint blocks are independent, so the
grid increments converge jointly; and the interpolation error is at most `2 / √n`, which
Mathlib's `tendstoInDistribution_of_tendstoInMeasure_sub` removes.

Mathlib has the central limit theorem for `(√n)⁻¹ ∑_{k < n} X k` and Brownian motion, but not
this statement. ATLAS's `donsker_invariance_principle` gives convergence in `C([0, 1])`.

Code-derived port of `BrownianFDD.brownian_fdd_convergence` and its helpers from
`v1/Atlas/FourierAnalysis/code/BrownianMotion.lean` at commit
`6191bf1ba03d204784385ef5be2472be88035b93`, lines 2387–2953 (Theorem 1 of Chapter 1, Brownian
Motion). The archived proof left two `sorry`s, the variable-block central limit theorem and
Slutsky's lemma for a deterministic perturbation; both are proved here. The public statement
inlines the archived `IsRademacher`, `fnIncrement` and `varianceVector` definitions. The archived
formalization and its original license/provenance remain in `v1/` (the original license text is
`v1/LICENSE`). This records equivalence to the archived Lean statement, not verification against
the printed textbook.
-/

set_option autoImplicit false

open MeasureTheory Complex Finset Filter
open scoped ENNReal NNReal Real Topology

namespace ProbabilityTheory

variable {m : ℕ}

/-- Predicate characterizing a Rademacher-type random variable $R : Ω → ℝ$ on
$(Ω, P)$: $R$ is measurable, has mean zero $\mathbb{E}[R] = \int R\,\mathrm{d}P = 0$,
and unit variance $\mathbb{E}[R^2] = \int R^2\,\mathrm{d}P = 1$. The canonical
example is the symmetric $\pm 1$ Bernoulli (Rademacher) variable. -/
structure IsRademacher {Ω : Type*} [MeasurableSpace Ω] (R : Ω → ℝ) (P : Measure Ω) : Prop where
  measurable : Measurable R
  mean_zero : ∫ ω, R ω ∂P = 0
  variance_one : ∫ ω, (R ω) ^ 2 ∂P = 1

/-- The $k$-th partial sum (random walk) of a sequence $(R_i)_{i \in ℕ}$ of random
variables: $S_k(ω) = \sum_{i < k} R_i(ω)$. -/
noncomputable def randomWalk {Ω : Type*} (R : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ range k, R i ω

/-- The Donsker-scaled increment of the random walk between indices $k_{\text{prev}}$
and $k_{\text{next}}$:
$$\frac{S_{k_{\text{next}}}(ω) - S_{k_{\text{prev}}}(ω)}{\sqrt{n}}.$$
This is the basic building block whose distribution converges to a Gaussian as
$n \to \infty$. -/
noncomputable def scaledIncrement {Ω : Type*} (R : ℕ → Ω → ℝ) (n : ℕ)
    (k_prev k_next : ℕ) (ω : Ω) : ℝ :=
  (randomWalk R k_next ω - randomWalk R k_prev ω) / Real.sqrt n

/-- The discrete grid index associated with a continuous time $t_j$ at scale $n$:
$\lfloor n \cdot t_j \rfloor$. Converts a continuous time partition into the nearest
discrete step on the random walk. -/
noncomputable def gridIndex (n : ℕ) (t : Fin (m + 1) → ℝ) (j : Fin (m + 1)) : ℕ :=
  ⌊(n : ℝ) * t j⌋₊

/-- The vector of variances $\sigma_j^2 = t_{j+1} - t_j$ for $j = 0, \dots, m-1$
associated with a strictly increasing time partition $t : \mathrm{Fin}(m+1) \to ℝ$.
These are the variances of the limiting independent Gaussian increments in Brownian
finite-dimensional distribution convergence. -/
noncomputable def varianceVector {m : ℕ} (t : Fin (m + 1) → ℝ) (ht : StrictMono t) :
    Fin m → NNReal :=
  fun j => ⟨t j.succ - t j.castSucc,
    le_of_lt (sub_pos.mpr (ht Fin.castSucc_lt_succ))⟩

/-- Monotonicity of the grid index: for a strictly monotone time partition $t$ and
fixed scale $n$, the discrete grid indices $j \mapsto \lfloor n \cdot t_j \rfloor$
form a monotone sequence. -/
lemma gridIndex_mono {m : ℕ} (n : ℕ) {t : Fin (m + 1) → ℝ}
    (ht : StrictMono t) :
    Monotone (fun j => gridIndex n t j) := by
  intro a b hab
  simp only [gridIndex]
  apply Nat.floor_le_floor
  exact mul_le_mul_of_nonneg_left (ht.monotone hab) (Nat.cast_nonneg n)

/-- The difference of partial sums equals the sum over the half-open interval:
$S_b(ω) - S_a(ω) = \sum_{i \in [a, b)} R_i(ω)$ for $a \le b$. -/
lemma randomWalk_diff_eq_sum_Ico {Ω : Type*} (R : ℕ → Ω → ℝ)
    {a b : ℕ} (hab : a ≤ b) (ω : Ω) :
    randomWalk R b ω - randomWalk R a ω = ∑ i ∈ Finset.Ico a b, R i ω := by
  simp only [randomWalk]
  have := Finset.sum_Ico_eq_sub (f := fun i => R i ω) hab
  linarith

/-- Rewrite the scaled increment as a normalized sum over a block:
$\dfrac{S_{k_{\text{next}}} - S_{k_{\text{prev}}}}{\sqrt{n}} =
\dfrac{1}{\sqrt{n}} \sum_{i \in [k_{\text{prev}}, k_{\text{next}})} R_i(ω)$. -/
lemma scaledIncrement_eq_sum_div {Ω : Type*} (R : ℕ → Ω → ℝ)
    (n : ℕ) {k_prev k_next : ℕ} (h : k_prev ≤ k_next) (ω : Ω) :
    scaledIncrement R n k_prev k_next ω =
      (∑ i ∈ Finset.Ico k_prev k_next, R i ω) / Real.sqrt n := by
  simp only [scaledIncrement]
  rw [randomWalk_diff_eq_sum_Ico R h ω]

/-- The ratio of block size to total scale converges to the time difference:
$$\frac{\lfloor n \cdot t_{j+1} \rfloor - \lfloor n \cdot t_j \rfloor}{n}
\;\longrightarrow\; t_{j+1} - t_j \quad (n \to \infty).$$
This is the key asymptotic that lets the rescaled increments carry the correct
Brownian variance in the limit. -/
theorem gridIndex_block_ratio_tendsto
    {m : ℕ} {t : Fin (m + 1) → ℝ} (ht : StrictMono t) (ht0 : 0 ≤ t 0)
    (j : Fin m) :
    Tendsto (fun n : ℕ => ((gridIndex n t j.succ - gridIndex n t j.castSucc : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds (t j.succ - t j.castSucc)) := by
  have hmono : ∀ n, gridIndex n t j.castSucc ≤ gridIndex n t j.succ := by
    intro n
    exact gridIndex_mono n ht (Fin.castSucc_lt_succ.le)
  have heq : (fun n : ℕ => ((gridIndex n t j.succ - gridIndex n t j.castSucc : ℕ) : ℝ) / (n : ℝ)) =
      (fun n : ℕ => (⌊(n : ℝ) * t j.succ⌋₊ : ℝ) / (n : ℝ) -
        (⌊(n : ℝ) * t j.castSucc⌋₊ : ℝ) / (n : ℝ)) := by
    ext n
    rw [Nat.cast_sub (hmono n)]
    simp only [gridIndex]
    ring
  rw [heq]
  have ht_succ : 0 ≤ t j.succ := le_trans ht0 (ht.monotone (Fin.zero_le _))
  have ht_cs : 0 ≤ t j.castSucc := le_trans ht0 (ht.monotone (Fin.zero_le _))
  have h1 : Tendsto (fun n : ℕ => (⌊(n : ℝ) * t j.succ⌋₊ : ℝ) / (n : ℝ))
      atTop (nhds (t j.succ)) := by
    have := (tendsto_nat_floor_mul_div_atTop ht_succ).comp tendsto_natCast_atTop_atTop
    simp only [mul_comm (t j.succ)] at this
    exact this
  have h2 : Tendsto (fun n : ℕ => (⌊(n : ℝ) * t j.castSucc⌋₊ : ℝ) / (n : ℝ))
      atTop (nhds (t j.castSucc)) := by
    have := (tendsto_nat_floor_mul_div_atTop ht_cs).comp tendsto_natCast_atTop_atTop
    simp only [mul_comm (t j.castSucc)] at this
    exact this
  exact h1.sub h2

/-- `n (φ(t/√n) - 1) → -t²/2` for the characteristic function `φ` of a centered unit-variance
law; the second-order Taylor expansion behind Mathlib's central limit theorem. -/
lemma tendsto_nat_mul_charFun_sub_one {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : AEMeasurable X P) (h0 : P[X] = 0) (h1 : P[X ^ 2] = 1) (t : ℝ) :
    Tendsto (fun n : ℕ => (n : ℂ) * (charFun (P.map X) ((√n)⁻¹ * t) - 1)) atTop
      (𝓝 (-(t : ℂ) ^ 2 / 2)) := by
  have hf : (fun n : ℕ ↦ charFun (P.map X) ((√n)⁻¹ * t) - (1 + (-(t : ℂ) ^ 2 / 2) / n)) =o[atTop]
      fun n ↦ 1 / (n : ℂ) := by
    suffices (fun (n : ℕ) ↦ charFun (Measure.map X P) ((√n)⁻¹ * t) -
        (1 + (-(((√n)⁻¹ * t) ^ 2 / 2) : ℂ))) =o[atTop] fun n ↦ ((√n)⁻¹ * t) ^ 2 by
      have aux : (fun (n : ℕ) ↦ ‖(1 / n : ℂ)‖) = fun (n : ℕ) ↦ ‖(1 / n : ℝ)‖ := by simp
      rw [← Asymptotics.isLittleO_norm_right, aux, Asymptotics.isLittleO_norm_right]
      refine .of_const_mul_right (c := t ^ 2) ?_
      convert! this using 4 with n <;> norm_cast <;> simp [field]
    have : Tendsto (fun (n : ℕ) ↦ (√n)⁻¹ * t) atTop (𝓝 0) := by
      rw [← zero_mul t]
      exact .mul_const t (tendsto_inv_atTop_zero.comp <| Real.tendsto_sqrt_atTop.comp
        tendsto_natCast_atTop_atTop)
    convert! (taylor_charFun_two hX h0 h1).comp_tendsto this using 2
    simp
    ring
  refine tendsto_sub_nhds_zero_iff.1 ?_
  convert hf.tendsto_inv_smul_nhds_zero.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n h0
  simp
  field_simp [n.cast_ne_zero.2 h0]
  ring

/-- If `n g n → w` and `m n / n → s`, then `(1 + g n) ^ m n → exp (s w)`. -/
lemma tendsto_one_add_pow_of_tendsto_nat_mul {g : ℕ → ℂ} {w : ℂ} {m : ℕ → ℕ} {s : ℝ}
    (hg : Tendsto (fun n : ℕ => (n : ℂ) * g n) atTop (𝓝 w))
    (hm : Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 s)) :
    Tendsto (fun n => (1 + g n) ^ m n) atTop (𝓝 (exp (s * w))) := by
  have hlog := tendsto_nat_mul_log_one_add_of_tendsto hg
  have hg0 : Tendsto g atTop (𝓝 0) := by
    have hinv : Tendsto (fun n : ℕ => (n : ℂ)⁻¹) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).ofReal
    have := hinv.mul hg
    rw [zero_mul] at this
    refine this.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    field_simp [n.cast_ne_zero.2 hn]
  have hprod : Tendsto (fun n : ℕ => (((m n : ℝ) / n : ℝ) : ℂ) * ((n : ℂ) * log (1 + g n)))
      atTop (𝓝 (s * w)) := (continuous_ofReal.tendsto s |>.comp hm).mul hlog
  refine ((continuous_exp.tendsto _).comp hprod).congr' ?_
  filter_upwards [eventually_ne_atTop 0, hg0.eventually_ne (show (0 : ℂ) ≠ -1 by simp)]
    with n hn hgn
  have h1 : 1 + g n ≠ 0 := fun h => hgn (by linear_combination h)
  simp only [Function.comp_apply]
  conv_rhs => rw [← exp_log h1, ← exp_nat_mul]
  congr 1
  push_cast
  field_simp [n.cast_ne_zero.2 hn]

/-- **Central limit theorem for variable blocks.** For iid centered unit-variance `R i`, if
`m n → ∞` and `m n / n → σ²`, then `(∑_{a n ≤ i < a n + m n} R i) / √n` converges in
distribution to `𝓝(0, σ²)`. -/
theorem variable_block_CLT_tendstoInDistribution
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {R : ℕ → Ω → ℝ}
    (hR_meas : ∀ i, Measurable (R i))
    (hR_mean : ∀ i, ∫ ω, R i ω ∂P = 0)
    (hR_var : ∀ i, ∫ ω, (R i ω) ^ 2 ∂P = 1)
    (hindep : iIndepFun R P)
    (hident : ∀ i, IdentDistrib (R i) (R 0) P P)
    (m_block : ℕ → ℕ) (a_block : ℕ → ℕ)
    (σ_sq : ℝ) (hσ_sq : 0 ≤ σ_sq)
    (hm_ratio : Tendsto (fun n => (m_block n : ℝ) / (n : ℝ)) atTop (nhds σ_sq))
    {Y : Ω' → ℝ}
    (hY : HasLaw Y (gaussianReal 0 ⟨σ_sq, hσ_sq⟩) P') :
    TendstoInDistribution
      (fun (n : ℕ) (ω : Ω) =>
        (∑ i ∈ Finset.Ico (a_block n) (a_block n + m_block n), R i ω) / Real.sqrt n)
      atTop Y (fun _ => P) P' where
  forall_aemeasurable n :=
    ((Finset.measurable_sum _ fun i _ => hR_meas i).div_const _).aemeasurable
  aemeasurable_limit := hY.aemeasurable
  tendsto := by
    refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t => ?_
    simp only [ProbabilityMeasure.coe_mk]
    rw [hY.map_eq]
    have hblock : ∀ n : ℕ, charFun (P.map fun ω =>
        (∑ i ∈ Finset.Ico (a_block n) (a_block n + m_block n), R i ω) / Real.sqrt n) t =
        charFun (P.map (R 0)) ((√n)⁻¹ * t) ^ m_block n := by
      intro n
      simp_rw [div_eq_inv_mul]
      rw [charFun_map_mul_comp (Finset.measurable_sum _ fun i _ => hR_meas i).aemeasurable,
        (hindep.restrict _).charFun_map_fun_finsetSum_eq_prod
          fun i _ => (hR_meas i).aemeasurable]
      simp [fun i => (hident i).map_eq]
    simp_rw [hblock]
    have h1 : P[R 0 ^ 2] = 1 := by simpa using hR_var 0
    have key := tendsto_one_add_pow_of_tendsto_nat_mul
      (tendsto_nat_mul_charFun_sub_one (hR_meas 0).aemeasurable (hR_mean 0) h1 t) hm_ratio
    have hfun : (fun n : ℕ => (1 + (charFun (P.map (R 0)) ((√n)⁻¹ * t) - 1)) ^ m_block n) =
        fun n : ℕ => charFun (P.map (R 0)) ((√n)⁻¹ * t) ^ m_block n := by
      funext n; ring
    rw [hfun] at key
    convert key using 2
    refine (charFun_gaussianReal t).trans ?_
    congr 1
    change (t : ℂ) * ((0 : ℝ) : ℂ) * I - ((σ_sq : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2 = _
    push_cast
    ring

/-- For iid Rademacher variables, the single scaled increment between grid points
$t_j$ and $t_{j+1}$ converges in distribution to a Gaussian with mean $0$ and
variance $\sigma_j^2 = t_{j+1} - t_j$. This is the one-dimensional marginal of
the Brownian FDD convergence, obtained by applying the variable-block CLT to the
block $[\lfloor n t_j \rfloor, \lfloor n t_{j+1} \rfloor)$. -/
theorem increment_tendstoInDistribution_gaussianReal
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {R : ℕ → Ω → ℝ}
    (hR : ∀ i, IsRademacher (R i) P)
    (hindep : iIndepFun (m := fun _ => inferInstance) R P)
    (hident : ∀ i, IdentDistrib (R i) (R 0) P P)
    {m : ℕ} (t : Fin (m + 1) → ℝ) (ht : StrictMono t) (ht0 : 0 ≤ t 0)
    (j : Fin m)
    {Y : Ω' → ℝ}
    (hY : HasLaw Y (gaussianReal 0 (varianceVector t ht j)) P') :
    TendstoInDistribution
      (fun (n : ℕ) (ω : Ω) =>
        scaledIncrement R n (gridIndex n t j.castSucc) (gridIndex n t j.succ) ω)
      atTop Y (fun _ => P) P' := by
  set m_block := fun n => gridIndex n t j.succ - gridIndex n t j.castSucc
  set a_block := fun n => gridIndex n t j.castSucc
  have hm_ratio : Tendsto (fun n => (m_block n : ℝ) / (n : ℝ)) atTop
      (nhds (t j.succ - t j.castSucc)) :=
    gridIndex_block_ratio_tendsto ht ht0 j
  have hσ_sq_nn : 0 ≤ t j.succ - t j.castSucc :=
    le_of_lt (sub_pos.mpr (ht Fin.castSucc_lt_succ))
  have hblock_sum : ∀ n, a_block n + m_block n = gridIndex n t j.succ := by
    intro n
    simp only [a_block, m_block]
    exact Nat.add_sub_cancel' (gridIndex_mono n ht (Fin.castSucc_lt_succ.le))
  have hfun_eq : (fun (n : ℕ) (ω : Ω) =>
      scaledIncrement R n (gridIndex n t j.castSucc) (gridIndex n t j.succ) ω) =
    (fun (n : ℕ) (ω : Ω) =>
      (∑ i ∈ Finset.Ico (a_block n) (a_block n + m_block n), R i ω) / Real.sqrt n) := by
    ext n ω
    rw [← hblock_sum]
    exact scaledIncrement_eq_sum_div R n (Nat.le_add_right _ _) ω
  rw [hfun_eq]
  have hvar_eq : varianceVector t ht j = ⟨t j.succ - t j.castSucc, hσ_sq_nn⟩ := by
    ext; rfl
  rw [hvar_eq] at hY
  exact variable_block_CLT_tendstoInDistribution
    (fun i => (hR i).measurable) (fun i => (hR i).mean_zero) (fun i => (hR i).variance_one)
    hindep hident m_block a_block
    (t j.succ - t j.castSucc) hσ_sq_nn hm_ratio hY

/-- Independence of $\sigma$-algebras indexed by disjoint families. Given an
$ι$-indexed independent family of $\sigma$-algebras $(m_i)$ and a $κ$-indexed
family of pairwise disjoint subsets $(S_j) \subseteq ι$, the bundled $\sigma$-algebras
$\bigvee_{i \in S_j} m_i$ are independent across $j$. -/
lemma iIndep_biSup_of_disjoint
    {Ω : Type*} {_mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {ι : Type*} {κ : Type*}
    {m : ι → MeasurableSpace Ω} (hm : ∀ i, m i ≤ _mΩ)
    (h_indep : iIndep m μ)
    {S : κ → Set ι} (hS : ∀ j₁ j₂ : κ, j₁ ≠ j₂ → Disjoint (S j₁) (S j₂)) :
    iIndep (fun j => ⨆ i ∈ S j, m i) μ := by
  classical
  rw [iIndep_iff]
  intro s f hf
  induction s using Finset.induction with
  | empty => simp [h_indep.isProbabilityMeasure.measure_univ]
  | insert j s hjs ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hf
    rw [Finset.prod_insert hjs]
    have ih' : μ (⋂ j' ∈ s, f j') = ∏ j' ∈ s, μ (f j') := ih hf.2
    have heq : (⋂ i ∈ insert j s, f i) = f j ∩ ⋂ i ∈ s, f i := by
      ext x; simp
    rw [heq, ← ih']
    have hdisj : Disjoint (S j) (⋃ j' ∈ (s : Set κ), S j') := by
      simp only [Set.disjoint_iUnion_right]
      intro j' hj'
      exact hS j j' (fun h => hjs (h ▸ hj'))
    have hindep_blocks : Indep (⨆ i ∈ S j, m i) (⨆ i ∈ (⋃ j' ∈ (s : Set κ), S j'), m i) μ :=
      indep_iSup_of_disjoint hm h_indep hdisj
    have hfj : @MeasurableSet Ω (⨆ i ∈ S j, m i) (f j) := hf.1
    have hle : (⨆ j' ∈ (s : Set κ), ⨆ i ∈ S j', m i) ≤
        ⨆ i ∈ (⋃ j' ∈ (s : Set κ), S j'), m i :=
      iSup₂_le fun j' hj' => iSup₂_le fun i hi =>
        le_iSup₂_of_le i (Set.mem_biUnion hj' hi) le_rfl
    have hfs : @MeasurableSet Ω (⨆ i ∈ (⋃ j' ∈ (s : Set κ), S j'), m i)
        (⋂ j' ∈ s, f j') := by
      apply hle
      apply MeasurableSet.biInter (Finset.countable_toSet s)
      intro j' hj'
      exact (le_iSup₂_of_le j' hj' le_rfl : ⨆ i ∈ S j', m i ≤ _) _ (hf.2 j' hj')
    have h_prod := hindep_blocks (f j) (⋂ j' ∈ s, f j') hfj hfs
    simp only [Kernel.const_apply, ae_dirac_eq] at h_prod
    exact h_prod

/-- The collection of scaled increments
$\bigl(\mathrm{scaledIncrement}\,R\,n\,\lfloor n t_j \rfloor\,\lfloor n t_{j+1} \rfloor\bigr)
_{j \in \mathrm{Fin}\,m}$
is jointly independent, because each increment is measurable with respect to the
$\sigma$-algebra generated by $(R_i)$ on a disjoint block of indices. -/
theorem increments_iIndepFun
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {R : ℕ → Ω → ℝ}
    (hindep : iIndepFun (m := fun _ => inferInstance) R P)
    (hR_meas : ∀ i, Measurable (R i))
    {m : ℕ} (t : Fin (m + 1) → ℝ) (ht : StrictMono t)
    (n : ℕ) :
    iIndepFun (m := fun (_ : Fin m) => inferInstance)
      (fun (j : Fin m) (ω : Ω) =>
        scaledIncrement R n (gridIndex n t j.castSucc) (gridIndex n t j.succ) ω) P := by
  let σR : ℕ → MeasurableSpace Ω := fun i => (inferInstance : MeasurableSpace ℝ).comap (R i)
  let block : Fin m → Set ℕ := fun j =>
    ((Finset.Ico (gridIndex n t j.castSucc) (gridIndex n t j.succ) : Finset ℕ) : Set ℕ)
  have hblock_disj : ∀ j₁ j₂ : Fin m, j₁ ≠ j₂ → Disjoint (block j₁) (block j₂) := by
    intro j₁ j₂ hne
    simp only [block, Finset.coe_Ico]
    have hmono := gridIndex_mono n ht
    rw [Set.disjoint_left]
    intro x hx1 hx2
    rcases lt_or_gt_of_ne hne with h | h
    · have hle := hmono (Fin.succ_le_castSucc_iff.mpr h)
      exact absurd (lt_of_lt_of_le hx1.2 (le_trans hle hx2.1)) (not_lt.mpr le_rfl)
    · have hle := hmono (Fin.succ_le_castSucc_iff.mpr h)
      exact absurd (lt_of_lt_of_le hx2.2 (le_trans hle hx1.1)) (not_lt.mpr le_rfl)
  have hσR_le : ∀ i, σR i ≤ ‹MeasurableSpace Ω› := fun i => (hR_meas i).comap_le
  have h_block_indep : iIndep (fun j => ⨆ i ∈ block j, σR i) P :=
    iIndep_biSup_of_disjoint hσR_le hindep hblock_disj
  have hincr_le : ∀ j : Fin m,
      (inferInstance : MeasurableSpace ℝ).comap
        (fun ω => scaledIncrement R n (gridIndex n t j.castSucc) (gridIndex n t j.succ) ω) ≤
      ⨆ i ∈ block j, σR i := by
    intro j
    have hle_block := gridIndex_mono n ht (@Fin.castSucc_lt_succ m j).le
    have heq : (fun ω => scaledIncrement R n (gridIndex n t j.castSucc) (gridIndex n t j.succ) ω) =
               (fun ω => (∑ i ∈ Finset.Ico (gridIndex n t j.castSucc) (gridIndex n t j.succ),
                 R i ω) / Real.sqrt n) := by
      ext ω; exact scaledIncrement_eq_sum_div R n hle_block ω
    rw [heq]
    exact (Measurable.div_const (Finset.measurable_sum _ fun i hi =>
      Measurable.mono (comap_measurable (R i))
        (le_iSup₂_of_le i (Finset.mem_coe.mpr hi) le_rfl) le_rfl) _).comap_le
  exact iIndep_of_iIndep_of_le h_block_indep hincr_le

/-- **Joint convergence from marginal convergence for independent coordinates.** If for
each $j$ the marginal sequence $X_n(j)$ converges in distribution to $Z(j)$, and if
the coordinates $(X_n(j))_j$ are jointly independent for every $n$ (and the limit
coordinates $(Z(j))_j$ are independent), then the full vector $X_n(\cdot)$ converges
in distribution to $Z(\cdot)$. -/
theorem indep_marginal_tendstoInDistribution_product
    {Ω Ω' : Type*} {m : ℕ}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (X : ℕ → Fin m → Ω → ℝ)
    (Z : Fin m → Ω' → ℝ)
    (hmarg : ∀ j : Fin m, TendstoInDistribution
      (fun n ω => X n j ω) atTop (Z j) (fun _ => P) P')
    (hindep : ∀ n, iIndepFun (m := fun (_ : Fin m) => inferInstance)
      (fun j ω => X n j ω) P)
    (hindep_limit : iIndepFun (m := fun (_ : Fin m) => inferInstance) Z P') :
    TendstoInDistribution
      (fun n ω => (fun j => X n j ω : Fin m → ℝ)) atTop
      (fun ω => (fun j => Z j ω : Fin m → ℝ)) (fun _ => P) P' where
  forall_aemeasurable n :=
    aemeasurable_pi_iff.mpr (fun j => (hmarg j).forall_aemeasurable n)
  aemeasurable_limit :=
    aemeasurable_pi_iff.mpr (fun j => (hmarg j).aemeasurable_limit)
  tendsto := by
    have hXaem : ∀ n j, AEMeasurable (fun ω => X n j ω) P :=
      fun n j => (hmarg j).forall_aemeasurable n
    have hZaem : ∀ j, AEMeasurable (Z j) P' :=
      fun j => (hmarg j).aemeasurable_limit
    have hmap_n : ∀ n, P.map (fun ω j => X n j ω) =
        Measure.pi (fun j => P.map (fun ω => X n j ω)) :=
      fun n => (iIndepFun_iff_map_fun_eq_pi_map (fun j => hXaem n j)).mp (hindep n)
    have hmap_lim : P'.map (fun ω j => Z j ω) =
        Measure.pi (fun j => P'.map (Z j)) :=
      (iIndepFun_iff_map_fun_eq_pi_map hZaem).mp hindep_limit
    have hpm_n : ∀ n j, IsProbabilityMeasure (P.map (fun ω => X n j ω)) :=
      fun _ _ => inferInstance
    have hpm_lim : ∀ j, IsProbabilityMeasure (P'.map (Z j)) :=
      fun _ => inferInstance
    let μ_n (n : ℕ) (j : Fin m) : ProbabilityMeasure ℝ :=
      ⟨P.map (fun ω => X n j ω), hpm_n n j⟩
    let μ_lim (j : Fin m) : ProbabilityMeasure ℝ :=
      ⟨P'.map (Z j), hpm_lim j⟩
    have hmarg_tendsto : ∀ j, Tendsto (fun n => μ_n n j) atTop (𝓝 (μ_lim j)) :=
      fun j => (hmarg j).tendsto
    have hpi_tendsto : Tendsto (fun n => ProbabilityMeasure.pi (μ_n n)) atTop
        (𝓝 (ProbabilityMeasure.pi μ_lim)) := by
      apply (ProbabilityMeasure.continuous_pi).continuousAt.tendsto.comp
      exact tendsto_pi_nhds.mpr hmarg_tendsto
    have hlim : ProbabilityMeasure.pi μ_lim = ⟨P'.map (fun ω j => Z j ω), inferInstance⟩ :=
      Subtype.ext hmap_lim.symm
    rw [hlim] at hpi_tendsto
    exact hpi_tendsto.congr fun n => Subtype.ext (hmap_n n).symm

/-- **Brownian FDD convergence (discrete version).** For iid Rademacher random
variables $(R_i)$, the vector of scaled increments on a partition
$0 \le t_0 < t_1 < \cdots < t_m$ converges jointly in distribution to a vector of
independent Gaussians with variances $\sigma_j^2 = t_{j+1} - t_j$. This combines
the one-dimensional CLT on each block (`increment_tendstoInDistribution_gaussianReal`)
with the joint-from-marginal-with-independence principle
(`indep_marginal_tendstoInDistribution_product`). -/
theorem brownian_fdd_convergence_discrete
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {R : ℕ → Ω → ℝ}
    (hR : ∀ i, IsRademacher (R i) P)
    (hindep : iIndepFun (m := fun _ => inferInstance) R P)
    (hident : ∀ i, IdentDistrib (R i) (R 0) P P)
    {m : ℕ} (t : Fin (m + 1) → ℝ) (ht : StrictMono t) (ht0 : 0 ≤ t 0)
    {Z : Fin m → Ω' → ℝ}
    (hZ : ∀ j, HasLaw (Z j) (gaussianReal 0 (varianceVector t ht j)) P')
    (hZindep : iIndepFun (m := fun (_ : Fin m) => inferInstance) Z P') :
    TendstoInDistribution
      (fun (n : ℕ) (ω : Ω) => (fun j : Fin m =>
        scaledIncrement R n (gridIndex n t j.castSucc) (gridIndex n t j.succ) ω))
      atTop
      (fun (ω : Ω') => (fun j : Fin m => Z j ω))
      (fun _ => P) P' := by
  apply indep_marginal_tendstoInDistribution_product
  · exact fun j =>
      increment_tendstoInDistribution_gaussianReal hR hindep hident t ht ht0 j (hZ j)
  · exact fun n => increments_iIndepFun hindep (fun i => (hR i).measurable) t ht n
  · exact hZindep

/-- The Donsker-scale piecewise linear interpolation $f_n(t)$ of the random walk:
between integer scaled times $k/n$ and $(k+1)/n$, the function interpolates linearly
between $S_k/\sqrt{n}$ and $S_{k+1}/\sqrt{n}$. Explicitly, with $k = \lfloor n t \rfloor$
and fractional part $\{nt\} = nt - k$,
$$f_n(t)(ω) = \frac{S_k(ω)}{\sqrt{n}} + \{nt\} \cdot \frac{R_k(ω)}{\sqrt{n}}.$$
This is the continuous-time process whose finite-dimensional distributions converge to
those of Brownian motion. -/
noncomputable def piecewiseLinearInterp {Ω : Type*} (R : ℕ → Ω → ℝ) (n : ℕ)
    (t : ℝ) (ω : Ω) : ℝ :=
  let k := ⌊(n : ℝ) * t⌋₊
  let frac := (n : ℝ) * t - ↑k
  randomWalk R k ω / Real.sqrt n + frac * R k ω / Real.sqrt n

/-- The continuous-time increment of the piecewise linear interpolation between
times $t_{\text{prev}}$ and $t_{\text{next}}$: $f_n(t_{\text{next}}) - f_n(t_{\text{prev}})$. -/
noncomputable def fnIncrement {Ω : Type*} (R : ℕ → Ω → ℝ) (n : ℕ)
    (t_prev t_next : ℝ) (ω : Ω) : ℝ :=
  piecewiseLinearInterp R n t_next ω - piecewiseLinearInterp R n t_prev ω

/-- Decomposition of the continuous-time increment of $f_n$ into the discrete scaled
increment plus a small fractional error:
$$f_n(t_{\text{next}}) - f_n(t_{\text{prev}}) =
\mathrm{scaledIncrement}\,R\,n\,\lfloor n t_{\text{prev}} \rfloor\,\lfloor n t_{\text{next}} \rfloor
+ \frac{1}{\sqrt{n}}\Bigl(\{n t_{\text{next}}\} R_{\lfloor n t_{\text{next}} \rfloor}
- \{n t_{\text{prev}}\} R_{\lfloor n t_{\text{prev}} \rfloor}\Bigr).$$
The error term is uniformly bounded by $2/\sqrt{n}$ (provided $|R_i| \le 1$) and so
vanishes in the limit; this is the basis of the Slutsky argument for
`brownian_fdd_convergence`. -/
lemma fnIncrement_eq_scaledIncrement_add_error {Ω : Type*} (R : ℕ → Ω → ℝ) (n : ℕ)
    (t_prev t_next : ℝ) (ω : Ω) :
    fnIncrement R n t_prev t_next ω =
      scaledIncrement R n ⌊(n : ℝ) * t_prev⌋₊ ⌊(n : ℝ) * t_next⌋₊ ω +
      (((n : ℝ) * t_next - ↑⌊(n : ℝ) * t_next⌋₊) * R ⌊(n : ℝ) * t_next⌋₊ ω -
       ((n : ℝ) * t_prev - ↑⌊(n : ℝ) * t_prev⌋₊) * R ⌊(n : ℝ) * t_prev⌋₊ ω) / Real.sqrt n := by
  simp only [fnIncrement, piecewiseLinearInterp, scaledIncrement, randomWalk]
  ring

/-- **Slutsky's theorem for deterministic perturbations.** If $X_n \Rightarrow Z$ in
distribution and $Y_n$ is uniformly close to $X_n$, with $\sup_ω \mathrm{dist}(Y_n(ω), X_n(ω))
\le \varepsilon_n \to 0$, then $Y_n \Rightarrow Z$ in distribution as well. This is the
standard tool for transferring distributional convergence across a vanishing additive
error term. -/
theorem slutsky_deterministic_perturbation
    {E : Type*} [SeminormedAddCommGroup E] [SecondCountableTopology E] [MeasurableSpace E]
    [BorelSpace E] {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {X Y : ℕ → Ω → E} {Z : Ω' → E}
    (ε : ℕ → ℝ)
    (hX : TendstoInDistribution X atTop Z (fun _ => P) P')
    (hY : ∀ n, AEMeasurable (Y n) P)
    (hclose : ∀ n ω, dist (Y n ω) (X n ω) ≤ ε n)
    (hε : Filter.Tendsto ε Filter.atTop (nhds 0)) :
    TendstoInDistribution Y atTop Z (fun _ => P) P' := by
  refine tendstoInDistribution_of_tendstoInMeasure_sub Y Z hX ?_ hY
  refine tendstoInMeasure_of_tendsto_ae
    (fun n => ((hY n).sub (hX.forall_aemeasurable n)).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hε
  simpa [dist_eq_norm] using hclose n ω

/-- **Theorem 1 — Brownian Motion (finite-dimensional distribution convergence).**
Let $(R_i)$ be iid Rademacher random variables with $|R_i| \le 1$. Then for any
strictly increasing time partition $0 \le t_0 < t_1 < \cdots < t_m$, the vector of
continuous-time increments
$$\bigl(f_n(t_1) - f_n(t_0),\; \dots,\; f_n(t_m) - f_n(t_{m-1})\bigr)$$
of the piecewise linear interpolation $f_n$ converges in distribution to a vector
of independent centered Gaussians with variances $\sigma_j^2 = t_j - t_{j-1}$.
Equivalently, the finite-dimensional distributions of $f_n$ converge to those of a
standard Brownian motion. The proof combines the discrete FDD convergence
(`brownian_fdd_convergence_discrete`) with Slutsky's theorem applied to the bounded
fractional error $\le 2/\sqrt{n}$ from `fnIncrement_eq_scaledIncrement_add_error`. -/
theorem brownian_fdd_convergence
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {R : ℕ → Ω → ℝ}
    (hR : ∀ i, IsRademacher (R i) P)
    (hindep : iIndepFun (m := fun _ => inferInstance) R P)
    (hident : ∀ i, IdentDistrib (R i) (R 0) P P)
    (hR_bdd : ∀ i ω, |R i ω| ≤ 1)
    {m : ℕ} (t : Fin (m + 1) → ℝ) (ht : StrictMono t) (ht0 : 0 ≤ t 0)
    {Z : Fin m → Ω' → ℝ}
    (hZ : ∀ j, HasLaw (Z j) (gaussianReal 0 (varianceVector t ht j)) P')
    (hZindep : iIndepFun (m := fun (_ : Fin m) => inferInstance) Z P') :
    TendstoInDistribution
      (fun (n : ℕ) (ω : Ω) => (fun j : Fin m =>
        fnIncrement R n (t j.castSucc) (t j.succ) ω))
      atTop
      (fun (ω : Ω') => (fun j : Fin m => Z j ω))
      (fun _ => P) P' := by
  have hRm : ∀ i, Measurable (R i) := fun i => (hR i).measurable
  exact slutsky_deterministic_perturbation (fun n => 2 / Real.sqrt n)
    (brownian_fdd_convergence_discrete hR hindep hident t ht ht0 hZ hZindep)
    (fun n => (measurable_pi_iff.mpr fun j => by
      simp only [fnIncrement, piecewiseLinearInterp, randomWalk]
      fun_prop).aemeasurable)
    (fun n ω => by
      apply (dist_pi_le_iff (by positivity : (0 : ℝ) ≤ 2 / Real.sqrt n)).mpr
      intro j
      rw [fnIncrement_eq_scaledIncrement_add_error, dist_eq_norm]
      simp only [gridIndex]
      have heq : scaledIncrement R n ⌊↑n * t j.castSucc⌋₊ ⌊↑n * t j.succ⌋₊ ω +
          ((↑n * t j.succ - ↑⌊↑n * t j.succ⌋₊) * R ⌊↑n * t j.succ⌋₊ ω -
          (↑n * t j.castSucc - ↑⌊↑n * t j.castSucc⌋₊) * R ⌊↑n * t j.castSucc⌋₊ ω) /
          Real.sqrt ↑n - scaledIncrement R n ⌊↑n * t j.castSucc⌋₊ ⌊↑n * t j.succ⌋₊ ω =
          ((↑n * t j.succ - ↑⌊↑n * t j.succ⌋₊) * R ⌊↑n * t j.succ⌋₊ ω -
          (↑n * t j.castSucc - ↑⌊↑n * t j.castSucc⌋₊) * R ⌊↑n * t j.castSucc⌋₊ ω) /
          Real.sqrt ↑n := by ring
      rw [heq, Real.norm_eq_abs]
      rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
      apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
      have hterm_bound : ∀ (s : ℝ), 0 ≤ s →
          |(↑n * s - ↑⌊↑n * s⌋₊) * R ⌊↑n * s⌋₊ ω| ≤ 1 := by
        intro s hs
        rw [abs_mul]
        calc |(↑n : ℝ) * s - ↑⌊↑n * s⌋₊| * |R ⌊↑n * s⌋₊ ω|
            ≤ 1 * 1 := by
              apply mul_le_mul _ (hR_bdd _ _) (abs_nonneg _) zero_le_one
              rw [abs_le]
              constructor
              · linarith [Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) hs)]
              · linarith [Nat.lt_floor_add_one ((↑n : ℝ) * s)]
          _ = 1 := one_mul 1
      calc |(↑n * t j.succ - ↑⌊↑n * t j.succ⌋₊) * R ⌊↑n * t j.succ⌋₊ ω -
              (↑n * t j.castSucc - ↑⌊↑n * t j.castSucc⌋₊) * R ⌊↑n * t j.castSucc⌋₊ ω|
          ≤ |(↑n * t j.succ - ↑⌊↑n * t j.succ⌋₊) * R ⌊↑n * t j.succ⌋₊ ω| +
            |(↑n * t j.castSucc - ↑⌊↑n * t j.castSucc⌋₊) * R ⌊↑n * t j.castSucc⌋₊ ω| :=
              abs_sub _ _
        _ ≤ 1 + 1 := add_le_add
            (hterm_bound _ (le_trans ht0 (ht.monotone (Fin.zero_le _))))
            (hterm_bound _ (le_trans ht0 (ht.monotone (Fin.zero_le _))))
        _ = 2 := by norm_num)
    (by
      have h2_0 : (2 : ℝ) * 0 = 0 := mul_zero 2
      rw [← h2_0]
      simp only [div_eq_mul_inv]
      exact (tendsto_const_nhds (x := (2 : ℝ))).mul
        (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)))

/-- **Finite-dimensional distributions of the rescaled random walk** (Theorem 1 of Chapter 1,
Brownian Motion). Let `R i` be iid with mean `0`, variance `1` and `|R i| ≤ 1`, and let
`f n s = S_{⌊ns⌋} / √n + (ns - ⌊ns⌋) R_{⌊ns⌋} / √n` with `S_k = ∑_{i < k} R i`. For times
`0 ≤ t 0 < ⋯ < t m` and independent `Z j ~ 𝓝(0, t (j + 1) - t j)`, the increments
`(f n (t (j + 1)) - f n (t j))_j` converge in distribution to `(Z j)_j`. -/
public theorem tendstoInDistribution_randomWalk_increments
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {R : ℕ → Ω → ℝ} (hR_meas : ∀ i, Measurable (R i)) (hR_mean : ∀ i, ∫ ω, R i ω ∂P = 0)
    (hR_var : ∀ i, ∫ ω, R i ω ^ 2 ∂P = 1) (hR_bdd : ∀ i ω, |R i ω| ≤ 1)
    (hindep : iIndepFun R P) (hident : ∀ i, IdentDistrib (R i) (R 0) P P)
    {m : ℕ} (t : Fin (m + 1) → ℝ) (ht : StrictMono t) (ht0 : 0 ≤ t 0)
    {Z : Fin m → Ω' → ℝ}
    (hZ : ∀ j, HasLaw (Z j) (gaussianReal 0 (t j.succ - t j.castSucc).toNNReal) P')
    (hZindep : iIndepFun Z P') :
    TendstoInDistribution
      (fun (n : ℕ) (ω : Ω) (j : Fin m) =>
        ((∑ i ∈ range ⌊(n : ℝ) * t j.succ⌋₊, R i ω) / √n +
            ((n : ℝ) * t j.succ - ⌊(n : ℝ) * t j.succ⌋₊) * R ⌊(n : ℝ) * t j.succ⌋₊ ω / √n) -
          ((∑ i ∈ range ⌊(n : ℝ) * t j.castSucc⌋₊, R i ω) / √n +
            ((n : ℝ) * t j.castSucc - ⌊(n : ℝ) * t j.castSucc⌋₊) *
              R ⌊(n : ℝ) * t j.castSucc⌋₊ ω / √n))
      atTop (fun ω j => Z j ω) (fun _ => P) P' := by
  have hZ' : ∀ j, HasLaw (Z j) (gaussianReal 0 (varianceVector t ht j)) P' := fun j => by
    convert hZ j using 2
    exact (Real.toNNReal_of_nonneg (sub_nonneg.2 (ht.monotone (Fin.castSucc_le_succ j)))).symm
  exact brownian_fdd_convergence (fun i => ⟨hR_meas i, hR_mean i, hR_var i⟩) hindep hident hR_bdd
    t ht ht0 hZ' hZindep

end ProbabilityTheory


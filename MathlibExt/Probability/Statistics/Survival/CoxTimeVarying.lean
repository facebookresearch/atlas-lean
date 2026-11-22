/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.CoxAsymptoticsVector
public import MathlibExt.Probability.Statistics.Survival.CoxAsymptotics

/-!
# Cox regression with time-dependent covariates (Andersen–Gill)

Each subject `l` carries a covariate *process* `t ↦ x l t ∈ ℝᵖ` instead of a fixed vector. With
observed times `Tᵢ`, event indicators `δᵢ` and risk sets `R(Tᵢ) = {l : T_l ≥ Tᵢ}`, Cox's partial
likelihood evaluates every covariate at the event time:

`L(β) = ∏_{i : δᵢ} exp ⟪β, xᵢ(Tᵢ)⟫ / ∑_{l ∈ R(Tᵢ)} exp ⟪β, x_l(Tᵢ)⟫`

(`tvPartialLikelihood`), with log partial likelihood `tvLogPartialLikelihood`, score vector
`U(β) = ∑_{i : δᵢ} (xᵢ(Tᵢ) - x̄ᵢ(β))` (`tvGradient`, `x̄ᵢ` the `exp ⟪β, x(Tᵢ)⟫`-weighted mean
over `R(Tᵢ)`) and observed information matrix `I(β) = ∑_{i : δᵢ} Covᵢ(β)` (`tvInfoMatrix`).
In counting-process form this is the Andersen–Gill partial likelihood
`∏_t ∏_i (Yᵢ(t) exp ⟪β, xᵢ(t)⟫ / ∑_l Y_l(t) exp ⟪β, x_l(t)⟫)^{ΔNᵢ(t)}` for one event per subject.

## Reduction to fixed covariates, event by event

The covariate matrix changes from event to event, so the time-dependent likelihood is not the
fixed-covariate likelihood of any one data set. It is, however, a sum over events of
fixed-covariate likelihoods: event `i` contributes the fixed-covariate likelihood
(`CoxPartialLikelihood`) of the data with the single event `i` (`eventAt i`) and the covariate
snapshot `l ↦ x l (Tᵢ)` (`snapshot x Tᵢ`). `tvLogPartialLikelihood_eq_sum`, `tvGradient_eq_sum`
and `tvInfoMatrix_eq_sum` state this; every analytic fact below is the corresponding
fixed-covariate fact of `CoxPartialLikelihood` and `CoxAsymptoticsVector`, summed over events.

## Main results

* `hasFDerivAt_tvLogPartialLikelihood`, `hasGradientAt_tvLogPartialLikelihood`: the score vector
  is the gradient of the log partial likelihood.
* `hasFDerivAt_tvGradient`: **the Jacobian of the score vector is `-I(β)`**.
* `concaveOn_tvLogPartialLikelihood`, `antitone_tvGradient_dotProduct`: concavity.
* `tvGradient_eq_zero_iff_isMaxOn`: the maximizers of the log partial likelihood are exactly the
  roots of the score.
* `tvLogPartialLikelihood_of_eq`, `tvGradient_of_eq`, `tvInfoMatrix_of_eq`: when the covariates
  agree at each event time with fixed covariates `z`, the time-dependent objects are the
  fixed-covariate ones of `CoxPartialLikelihood` / `CoxAsymptoticsVector`.
* For a scalar time-dependent covariate `z l t`: `isConcaveScore_tv` (the log partial likelihood
  is a concave criterion in the sense of `ConcaveScore`), and the Andersen–Gill theorems
  `tendsto_measure_not_exists_isMaxOn_tv` (existence with probability tending to one),
  `tendstoInMeasure_tvMPLE` (**consistency**), `tendstoInDistribution_tvMPLE` and
  `tendstoInDistribution_tvMPLE_gaussian` (**asymptotic normality**,
  `√n (βhat n - β₀) ⟶ Z / v ~ N(0, v⁻¹)`), and `tendstoInMeasure_tvInformation_tvMPLE`
  (`Iₙ(βhat n) / n → v`).

## Scope

As in `CoxAsymptotics`, the two limit hypotheses (score limit, uniform information limit) are
assumed, not derived from the counting-process conditions (Rebolledo's martingale CLT under
predictability of the covariate processes, Lenglart's inequality, the uniform law for
`S⁽ᵏ⁾ / n`). The large-sample theorems are proved for a **scalar** time-dependent covariate.
The vector large-sample theorems of `CoxAsymptoticsVector` are stated for the fixed-covariate
score `coxGradient` itself; their time-dependent analogues would need that argument restated
for an abstract concave criterion on `ℝᵖ` (a vector form of `ConcaveScore`) and are not
covered. Recurrent events and delayed entry (general at-risk indicators `Y_l(t)`) are not
covered: risk sets are `{l : T_l ≥ Tᵢ}`.

## References

* P. K. Andersen and R. D. Gill, *Cox's regression model for counting processes: a large sample
  study*, Ann. Statist. 10 (1982), 1100–1120.
* D. R. Cox, *Regression models and life-tables*, J. Roy. Statist. Soc. Ser. B 34 (1972),
  187–220, Section 8 (time-dependent covariates).
* J. D. Kalbfleisch and R. L. Prentice, *The Statistical Analysis of Failure Time Data*, 2nd ed.,
  Wiley, 2002, Section 6.4.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.CoxTimeVarying

open MeasureTheory ProbabilityTheory Filter Topology Finset Real Matrix
open MathlibExt.Probability.Statistics.CoxPartialLikelihood
open MathlibExt.Probability.Statistics.CoxAsymptoticsVector
open MathlibExt.Probability.Statistics.ConcaveScore

/-! ### Definitions -/

section Deterministic

variable {n p : ℕ}

/-- The covariate vectors of all subjects at time `t`. -/
def snapshot (x : Fin n → ℝ → Fin p → ℝ) (t : ℝ) : Fin n → Fin p → ℝ := fun l => x l t

/-- The event indicator of the data set in which subject `i` is the only event. -/
def eventAt (i : Fin n) : Fin n → Bool := fun l => decide (l = i)

/-- A sum over the events of `eventAt i` is the term of `i`. -/
theorem sum_filter_eventAt {M : Type*} [AddCommMonoid M] (i : Fin n) (F : Fin n → M) :
    ∑ k with eventAt i k = true, F k = F i := by
  simp [eventAt, Finset.filter_eq']

/-- Cox's partial likelihood with time-dependent covariates,
`∏_{i : δᵢ} exp ⟪β, xᵢ(Tᵢ)⟫ / ∑_{l ∈ R(Tᵢ)} exp ⟪β, x_l(Tᵢ)⟫`. -/
noncomputable def tvPartialLikelihood (T : Fin n → ℝ) (δ : Fin n → Bool)
    (x : Fin n → ℝ → Fin p → ℝ) (β : Fin p → ℝ) : ℝ :=
  ∏ i with δ i = true, exp (β ⬝ᵥ x i (T i)) / ∑ l ∈ riskSet T i, exp (β ⬝ᵥ x l (T i))

/-- The log partial likelihood with time-dependent covariates,
`∑_{i : δᵢ} (⟪β, xᵢ(Tᵢ)⟫ - log ∑_{l ∈ R(Tᵢ)} exp ⟪β, x_l(Tᵢ)⟫)`. -/
noncomputable def tvLogPartialLikelihood (T : Fin n → ℝ) (δ : Fin n → Bool)
    (x : Fin n → ℝ → Fin p → ℝ) (β : Fin p → ℝ) : ℝ :=
  ∑ i with δ i = true, (β ⬝ᵥ x i (T i) - log (∑ l ∈ riskSet T i, exp (β ⬝ᵥ x l (T i))))

/-- The score vector with time-dependent covariates, `∑_{i : δᵢ} (xᵢ(Tᵢ) - x̄ᵢ(β))`, where
`x̄ᵢ(β)` is the `exp ⟪β, x(Tᵢ)⟫`-weighted mean of the covariates at time `Tᵢ` over `R(Tᵢ)`. -/
noncomputable def tvGradient (T : Fin n → ℝ) (δ : Fin n → Bool) (x : Fin n → ℝ → Fin p → ℝ)
    (β : Fin p → ℝ) : Fin p → ℝ :=
  ∑ i with δ i = true, (x i (T i) - riskMeanVec T (snapshot x (T i)) β i)

/-- The observed information matrix with time-dependent covariates, `∑_{i : δᵢ} Covᵢ(β)`, the sum
of the weighted covariance matrices of the covariates at time `Tᵢ` over `R(Tᵢ)`. -/
noncomputable def tvInfoMatrix (T : Fin n → ℝ) (δ : Fin n → Bool) (x : Fin n → ℝ → Fin p → ℝ)
    (β : Fin p → ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  ∑ i with δ i = true, riskCov T (snapshot x (T i)) β i

variable (T : Fin n → ℝ) (δ : Fin n → Bool) (x : Fin n → ℝ → Fin p → ℝ)

/-- The logarithm of the partial likelihood is the log partial likelihood. -/
theorem log_tvPartialLikelihood (β : Fin p → ℝ) :
    log (tvPartialLikelihood T δ x β) = tvLogPartialLikelihood T δ x β := by
  have hpos : ∀ i, 0 < ∑ l ∈ riskSet T i, exp (β ⬝ᵥ x l (T i)) := fun i =>
    sum_pos (fun _ _ => exp_pos _) (riskSet_nonempty T i)
  rw [tvPartialLikelihood, tvLogPartialLikelihood, log_prod]
  · refine sum_congr rfl fun i _ => ?_
    rw [log_div (exp_pos _).ne' (hpos i).ne', log_exp]
  · exact fun i _ => (div_pos (exp_pos _) (hpos i)).ne'

/-! ### The event-by-event decomposition -/

/-- **The time-dependent log partial likelihood is a sum of fixed-covariate ones**: event `i`
contributes the fixed-covariate log partial likelihood of the single event `i` with the
covariates frozen at `Tᵢ`. -/
theorem tvLogPartialLikelihood_eq_sum (β : Fin p → ℝ) :
    tvLogPartialLikelihood T δ x β =
      ∑ i with δ i = true, logPartialLikelihood T (eventAt i) (snapshot x (T i)) β := by
  refine sum_congr rfl fun i _ => ?_
  rw [logPartialLikelihood, sum_filter_eventAt]
  rfl

/-- The time-dependent score vector is the sum over events of the fixed-covariate score vectors
of the single event `i` with the covariates frozen at `Tᵢ`. -/
theorem tvGradient_eq_sum (β : Fin p → ℝ) :
    tvGradient T δ x β =
      ∑ i with δ i = true, coxGradient T (eventAt i) (snapshot x (T i)) β := by
  refine sum_congr rfl fun i _ => ?_
  rw [coxGradient, sum_filter_eventAt]
  rfl

/-- The time-dependent information matrix is the sum over events of the fixed-covariate
information matrices of the single event `i` with the covariates frozen at `Tᵢ`. -/
theorem tvInfoMatrix_eq_sum (β : Fin p → ℝ) :
    tvInfoMatrix T δ x β =
      ∑ i with δ i = true, coxInfoMatrix T (eventAt i) (snapshot x (T i)) β := by
  refine sum_congr rfl fun i _ => ?_
  rw [coxInfoMatrix, sum_filter_eventAt]

/-! ### Calculus and concavity -/

/-- The Fréchet derivative of the time-dependent log partial likelihood at `β` is
`v ↦ ⟪v, U(β)⟫`, with `U = tvGradient` the score vector. -/
theorem hasFDerivAt_tvLogPartialLikelihood (β : Fin p → ℝ) :
    HasFDerivAt (tvLogPartialLikelihood T δ x) (Real.dotL (tvGradient T δ x β)) β := by
  have h : HasFDerivAt
      (fun b => ∑ i with δ i = true, logPartialLikelihood T (eventAt i) (snapshot x (T i)) b)
      (∑ i with δ i = true, Real.dotL (coxGradient T (eventAt i) (snapshot x (T i)) β)) β :=
    HasFDerivAt.fun_sum fun i _ =>
      hasFDerivAt_logPartialLikelihood T (eventAt i) (snapshot x (T i)) β
  rw [show tvLogPartialLikelihood T δ x = _ from funext (tvLogPartialLikelihood_eq_sum T δ x),
    tvGradient_eq_sum]
  convert h using 1
  ext v
  simp [Real.dotL_apply, dotProduct_sum]

/-- **The time-dependent score vector is the gradient of the log partial likelihood**, in
Euclidean space `EuclideanSpace ℝ (Fin p)`. -/
theorem hasGradientAt_tvLogPartialLikelihood (β : Fin p → ℝ) :
    HasGradientAt (fun b : EuclideanSpace ℝ (Fin p) => tvLogPartialLikelihood T δ x b.ofLp)
      (WithLp.toLp 2 (tvGradient T δ x β)) (WithLp.toLp 2 β) :=
  Real.hasGradientAt_ofLp (hasFDerivAt_tvLogPartialLikelihood T δ x β)

/-- **The Jacobian of the time-dependent score vector is minus the information matrix.** -/
theorem hasFDerivAt_tvGradient (β : Fin p → ℝ) :
    HasFDerivAt (tvGradient T δ x) (-mulVecCLM (tvInfoMatrix T δ x β)) β := by
  have h : HasFDerivAt
      (fun b => ∑ i with δ i = true, coxGradient T (eventAt i) (snapshot x (T i)) b)
      (∑ i with δ i = true, -mulVecCLM (coxInfoMatrix T (eventAt i) (snapshot x (T i)) β)) β :=
    HasFDerivAt.fun_sum fun i _ => hasFDerivAt_coxGradient T (eventAt i) (snapshot x (T i)) β
  rw [show tvGradient T δ x = _ from funext (tvGradient_eq_sum T δ x), tvInfoMatrix_eq_sum,
    mulVecCLM_sum, ← sum_neg_distrib]
  exact h

/-- **The time-dependent log partial likelihood is concave.** -/
theorem concaveOn_tvLogPartialLikelihood :
    ConcaveOn ℝ Set.univ (tvLogPartialLikelihood T δ x) := by
  rw [show tvLogPartialLikelihood T δ x = _ from funext (tvLogPartialLikelihood_eq_sum T δ x)]
  refine ⟨convex_univ, fun β _ γ _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun i _ => ?_
  simpa only [smul_eq_mul] using
    (concaveOn_logPartialLikelihood T (eventAt i) (snapshot x (T i))).2
      (Set.mem_univ β) (Set.mem_univ γ) ha hb hab

/-- **The time-dependent score is antitone along every line**: `t ↦ ⟪U(β + t u), u⟫`. -/
theorem antitone_tvGradient_dotProduct (β u : Fin p → ℝ) :
    Antitone fun t : ℝ => tvGradient T δ x (β + t • u) ⬝ᵥ u := by
  intro s t hst
  simp only [tvGradient_eq_sum, sum_dotProduct]
  exact sum_le_sum fun i _ =>
    antitone_coxGradient_dotProduct T (eventAt i) (snapshot x (T i)) β u hst

/-- A maximizer of the time-dependent log partial likelihood is a root of the score. -/
theorem tvGradient_eq_zero_of_isMaxOn {b : Fin p → ℝ}
    (h : IsMaxOn (tvLogPartialLikelihood T δ x) Set.univ b) : tvGradient T δ x b = 0 := by
  have h0 := (h.isLocalMax Filter.univ_mem).hasFDerivAt_eq_zero
    (hasFDerivAt_tvLogPartialLikelihood T δ x b)
  funext j
  have := congrArg (fun L => L (Pi.single j 1)) h0
  simpa [Real.dotL_apply, single_dotProduct] using this

/-- A root of the time-dependent score maximizes the log partial likelihood. -/
theorem isMaxOn_of_tvGradient_eq_zero {b : Fin p → ℝ} (h : tvGradient T δ x b = 0) :
    IsMaxOn (tvLogPartialLikelihood T δ x) Set.univ b := by
  intro y _
  set d := y - b with hd
  set g : ℝ → ℝ := fun t => tvLogPartialLikelihood T δ x (b + t • d) with hgdef
  have hg : ∀ t, HasDerivAt g (tvGradient T δ x (b + t • d) ⬝ᵥ d) t := fun t => by
    have := (hasFDerivAt_tvLogPartialLikelihood T δ x (b + t • d)).comp_hasDerivAt t
      (((hasDerivAt_id t).smul_const d).const_add b)
    rw [dotProduct_comm]
    simpa [Real.dotL_apply, Function.comp_def] using this
  have hanti := antitone_tvGradient_dotProduct T δ x b d
  have hmono : AntitoneOn g (Set.Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun t _ => (hg t).continuousAt.continuousWithinAt)
      (fun t _ => (hg t).differentiableAt.differentiableWithinAt) fun t ht => ?_
    rw [interior_Ici] at ht
    rw [(hg t).deriv]
    have := hanti (le_of_lt ht)
    simp only [zero_smul, add_zero, h, zero_dotProduct] at this
    exact this
  have h01 := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 zero_le_one) zero_le_one
  simp only [hgdef, one_smul, zero_smul, add_zero, hd, add_sub_cancel] at h01
  exact h01

/-- **The maximizers of the time-dependent log partial likelihood are the roots of the score.** -/
theorem tvGradient_eq_zero_iff_isMaxOn (b : Fin p → ℝ) :
    tvGradient T δ x b = 0 ↔ IsMaxOn (tvLogPartialLikelihood T δ x) Set.univ b :=
  ⟨isMaxOn_of_tvGradient_eq_zero T δ x, tvGradient_eq_zero_of_isMaxOn T δ x⟩

/-! ### Covariates that are fixed at the event times -/

variable {T δ x}

/-- If at every event time the covariates equal fixed covariates `z`, the time-dependent log
partial likelihood is the fixed-covariate one. -/
theorem tvLogPartialLikelihood_of_eq {z : Fin n → Fin p → ℝ}
    (hx : ∀ i, δ i = true → ∀ l, x l (T i) = z l) (β : Fin p → ℝ) :
    tvLogPartialLikelihood T δ x β = logPartialLikelihood T δ z β :=
  sum_congr rfl fun i hi => by
    have hi := hx i (mem_filter.1 hi).2
    simp only [hi]

/-- If at every event time the covariates equal fixed covariates `z`, the time-dependent score
vector is the fixed-covariate one. -/
theorem tvGradient_of_eq {z : Fin n → Fin p → ℝ}
    (hx : ∀ i, δ i = true → ∀ l, x l (T i) = z l) (β : Fin p → ℝ) :
    tvGradient T δ x β = coxGradient T δ z β :=
  sum_congr rfl fun i hi => by
    have hi := hx i (mem_filter.1 hi).2
    have hs : snapshot x (T i) = z := funext hi
    rw [hs, hi]

/-- If at every event time the covariates equal fixed covariates `z`, the time-dependent
information matrix is the fixed-covariate one. -/
theorem tvInfoMatrix_of_eq {z : Fin n → Fin p → ℝ}
    (hx : ∀ i, δ i = true → ∀ l, x l (T i) = z l) (β : Fin p → ℝ) :
    tvInfoMatrix T δ x β = coxInfoMatrix T δ z β :=
  sum_congr rfl fun i hi => by
    have hs : snapshot x (T i) = z := funext (hx i (mem_filter.1 hi).2)
    rw [hs]

end Deterministic

/-! ### A scalar time-dependent covariate -/

section Scalar

variable {n : ℕ}

/-- The time-dependent log partial likelihood of a scalar covariate process `z l t`, as a
function of `b ∈ ℝ`. -/
noncomputable def tvLogPartialLikelihood₁ (T : Fin n → ℝ) (δ : Fin n → Bool)
    (z : Fin n → ℝ → ℝ) (b : ℝ) : ℝ :=
  tvLogPartialLikelihood T δ (fun l t (_ : Fin 1) => z l t) (fun _ => b)

/-- The time-dependent Cox score of a scalar covariate process:
`∑_{i : δᵢ} (zᵢ(Tᵢ) - z̄ᵢ(b))`, with `z̄ᵢ(b)` the `exp (b z(Tᵢ))`-weighted mean over `R(Tᵢ)`. -/
noncomputable def tvScore (T : Fin n → ℝ) (δ : Fin n → Bool) (z : Fin n → ℝ → ℝ) (b : ℝ) : ℝ :=
  ∑ i with δ i = true, (z i (T i) - riskMean T (fun l => z l (T i)) b i)

/-- The time-dependent Cox information of a scalar covariate process: `∑_{i : δᵢ} Varᵢ(b)`, the
weighted variances of `z(Tᵢ)` over `R(Tᵢ)`. -/
noncomputable def tvInformation (T : Fin n → ℝ) (δ : Fin n → Bool) (z : Fin n → ℝ → ℝ)
    (b : ℝ) : ℝ :=
  ∑ i with δ i = true, riskVar T (fun l => z l (T i)) b i

variable (T : Fin n → ℝ) (δ : Fin n → Bool) (z : Fin n → ℝ → ℝ)

/-- The scalar time-dependent log partial likelihood is the sum over events of the scalar
fixed-covariate ones of the single event `i` with the covariate frozen at `Tᵢ`. -/
theorem tvLogPartialLikelihood₁_eq_sum (b : ℝ) :
    tvLogPartialLikelihood₁ T δ z b =
      ∑ i with δ i = true, logPartialLikelihood₁ T (eventAt i) (fun l => z l (T i)) b := by
  rw [tvLogPartialLikelihood₁, tvLogPartialLikelihood_eq_sum]
  rfl

/-- The scalar time-dependent score is the sum over events of the scalar fixed-covariate scores
of the single event `i` with the covariate frozen at `Tᵢ`. -/
theorem tvScore_eq_sum (b : ℝ) :
    tvScore T δ z b = ∑ i with δ i = true, coxScore T (eventAt i) (fun l => z l (T i)) b := by
  refine sum_congr rfl fun i _ => ?_
  rw [coxScore, sum_filter_eventAt]

/-- The scalar time-dependent information is the sum over events of the scalar fixed-covariate
informations of the single event `i` with the covariate frozen at `Tᵢ`. -/
theorem tvInformation_eq_sum (b : ℝ) :
    tvInformation T δ z b =
      ∑ i with δ i = true, coxInformation T (eventAt i) (fun l => z l (T i)) b := by
  refine sum_congr rfl fun i _ => ?_
  rw [coxInformation, sum_filter_eventAt]

/-- For one covariate the score vector has the scalar score `tvScore` as its single
component. -/
theorem tvGradient_one (b : ℝ) :
    tvGradient T δ (fun l t (_ : Fin 1) => z l t) (fun _ => b) = fun _ => tvScore T δ z b := by
  rw [tvGradient_eq_sum, tvScore_eq_sum]
  funext j
  simp only [Finset.sum_apply]
  exact sum_congr rfl fun i _ =>
    congrFun (coxGradient_one T (eventAt i) (fun l => z l (T i)) b) j

/-- **The scalar time-dependent log partial likelihood is a concave criterion** with score
`tvScore` and information `tvInformation`. -/
theorem isConcaveScore_tv :
    IsConcaveScore (tvLogPartialLikelihood₁ T δ z) (tvScore T δ z) (tvInformation T δ z) := by
  refine ⟨fun b => ?_, fun b => ?_, fun b => ?_⟩
  · rw [show tvLogPartialLikelihood₁ T δ z = _ from funext (tvLogPartialLikelihood₁_eq_sum T δ z),
      tvScore_eq_sum]
    exact HasDerivAt.fun_sum fun i _ =>
      hasDerivAt_logPartialLikelihood T (eventAt i) (fun l => z l (T i)) b
  · rw [show tvScore T δ z = _ from funext (tvScore_eq_sum T δ z), tvInformation_eq_sum,
      ← sum_neg_distrib]
    exact HasDerivAt.fun_sum fun i _ => hasDerivAt_coxScore T (eventAt i) (fun l => z l (T i)) b
  · rw [tvInformation_eq_sum]
    exact sum_nonneg fun i _ =>
      CoxAsymptotics.coxInformation_nonneg T (eventAt i) (fun l => z l (T i)) b

variable {T δ z}

/-- If at every event time the scalar covariates equal fixed covariates `z'`, the time-dependent
score is the fixed-covariate score `coxScore`. -/
theorem tvScore_of_eq {z' : Fin n → ℝ} (hz : ∀ i, δ i = true → ∀ l, z l (T i) = z' l) (b : ℝ) :
    tvScore T δ z b = coxScore T δ z' b :=
  sum_congr rfl fun i hi => by
    have hi := hz i (mem_filter.1 hi).2
    have hs : (fun l => z l (T i)) = z' := funext hi
    rw [hs, hi]

/-- If at every event time the scalar covariates equal fixed covariates `z'`, the time-dependent
information is the fixed-covariate information `coxInformation`. -/
theorem tvInformation_of_eq {z' : Fin n → ℝ} (hz : ∀ i, δ i = true → ∀ l, z l (T i) = z' l)
    (b : ℝ) : tvInformation T δ z b = coxInformation T δ z' b :=
  sum_congr rfl fun i hi => by
    have hs : (fun l => z l (T i)) = z' := funext (hz i (mem_filter.1 hi).2)
    rw [hs]

end Scalar

/-! ### The Andersen–Gill theorems for a scalar time-dependent covariate -/

section AndersenGill

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {T : (n : ℕ) → Ω → Fin n → ℝ} {δ : (n : ℕ) → Ω → Fin n → Bool}
  {z : (n : ℕ) → Ω → Fin n → ℝ → ℝ} {βhat : ℕ → Ω → ℝ} {β₀ r : ℝ} {i : ℝ → ℝ} {Z : Ω' → ℝ}
  {v : NNReal}

/-- **Existence of the time-dependent Cox estimator with probability tending to one.** Under the
Andersen–Gill hypotheses (score limit at `β₀`, uniform convergence in probability of
`Iₙ(b) / n` near `β₀` to a function `i` continuous at `β₀` with `i β₀ = v > 0`), the probability
that the log partial likelihood has no maximizer tends to zero. -/
theorem tendsto_measure_not_exists_isMaxOn_tv (hv : v ≠ 0)
    (hscore : TendstoInDistribution
      (fun (n : ℕ) ω ↦ tvScore (T n ω) (δ n ω) (z n ω) β₀ / √(n : ℝ)) atTop Z (fun _ ↦ P) P')
    (hi : ContinuousAt i β₀) (hiv : i β₀ = v)
    (hinfo : ∀ η > 0, Tendsto (fun n : ℕ => P {ω | ∃ b ∈ Set.Icc (β₀ - r) (β₀ + r),
      η ≤ |tvInformation (T n ω) (δ n ω) (z n ω) b / n - i b|}) atTop (𝓝 0))
    (hr : 0 < r) :
    Tendsto (fun n : ℕ => P {ω | ¬ ∃ b,
      IsMaxOn (tvLogPartialLikelihood₁ (T n ω) (δ n ω) (z n ω)) Set.univ b}) atTop (𝓝 0) :=
  ConcaveScore.tendsto_measure_not_exists_isMaxOn
    (fun n ω => isConcaveScore_tv (T n ω) (δ n ω) (z n ω)) hv hscore hi hiv hinfo hr

/-- **Consistency of the time-dependent Cox estimator** (Andersen–Gill 1982, Theorem 3.2, scalar
time-dependent covariate). Let `βhat n` be a maximizer of the time-dependent log partial
likelihood whenever one exists. If `Uₙ(β₀) / √n` converges in distribution and `Iₙ(b) / n`
converges uniformly in probability on `[β₀ - r, β₀ + r]` to a function `i` continuous at `β₀`
with `i(β₀) = v > 0`, then `βhat n → β₀` in probability. -/
theorem tendstoInMeasure_tvMPLE (hv : v ≠ 0)
    (hβhat : ∀ n ω, (∃ b, IsMaxOn (tvLogPartialLikelihood₁ (T n ω) (δ n ω) (z n ω)) Set.univ b) →
      IsMaxOn (tvLogPartialLikelihood₁ (T n ω) (δ n ω) (z n ω)) Set.univ (βhat n ω))
    (hscore : TendstoInDistribution
      (fun (n : ℕ) ω ↦ tvScore (T n ω) (δ n ω) (z n ω) β₀ / √(n : ℝ)) atTop Z (fun _ ↦ P) P')
    (hi : ContinuousAt i β₀) (hiv : i β₀ = v)
    (hinfo : ∀ η > 0, Tendsto (fun n : ℕ => P {ω | ∃ b ∈ Set.Icc (β₀ - r) (β₀ + r),
      η ≤ |tvInformation (T n ω) (δ n ω) (z n ω) b / n - i b|}) atTop (𝓝 0))
    (hr : 0 < r) :
    TendstoInMeasure P βhat atTop (fun _ => β₀) :=
  tendstoInMeasure_argmax
    (fun n ω => isConcaveScore_tv (T n ω) (δ n ω) (z n ω)) hv hβhat hscore hi hiv hinfo hr

/-- **The time-dependent Cox estimator is asymptotically `Z / v`.** Under the hypotheses of
`tendstoInMeasure_tvMPLE` and measurability of the estimator, `√n (βhat n - β₀) ⟶ Z / v` in
distribution, `Z` the limit of `Uₙ(β₀) / √n` and `v = i(β₀)`. -/
theorem tendstoInDistribution_tvMPLE (hv : v ≠ 0)
    (hβhat : ∀ n ω, (∃ b, IsMaxOn (tvLogPartialLikelihood₁ (T n ω) (δ n ω) (z n ω)) Set.univ b) →
      IsMaxOn (tvLogPartialLikelihood₁ (T n ω) (δ n ω) (z n ω)) Set.univ (βhat n ω))
    (hβhat_meas : ∀ n, AEMeasurable (βhat n) P)
    (hscore : TendstoInDistribution
      (fun (n : ℕ) ω ↦ tvScore (T n ω) (δ n ω) (z n ω) β₀ / √(n : ℝ)) atTop Z (fun _ ↦ P) P')
    (hi : ContinuousAt i β₀) (hiv : i β₀ = v)
    (hinfo : ∀ η > 0, Tendsto (fun n : ℕ => P {ω | ∃ b ∈ Set.Icc (β₀ - r) (β₀ + r),
      η ≤ |tvInformation (T n ω) (δ n ω) (z n ω) b / n - i b|}) atTop (𝓝 0))
    (hr : 0 < r) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) * (βhat n ω - β₀)) atTop
      (fun ω => Z ω / (v : ℝ)) (fun _ ↦ P) P' :=
  tendstoInDistribution_argmax
    (fun n ω => isConcaveScore_tv (T n ω) (δ n ω) (z n ω)) hv hβhat hβhat_meas hscore hi hiv
    hinfo hr

/-- **Asymptotic normality of the time-dependent Cox estimator** (Andersen–Gill 1982, Theorem 3.3,
scalar time-dependent covariate). If moreover `Z ~ N(0, v)`, then `√n (βhat n - β₀) ⟶ Z / v`
and `Z / v ~ N(0, v⁻¹)`: the asymptotic variance is the inverse of the limiting information. -/
theorem tendstoInDistribution_tvMPLE_gaussian (hv : v ≠ 0)
    (hβhat : ∀ n ω, (∃ b, IsMaxOn (tvLogPartialLikelihood₁ (T n ω) (δ n ω) (z n ω)) Set.univ b) →
      IsMaxOn (tvLogPartialLikelihood₁ (T n ω) (δ n ω) (z n ω)) Set.univ (βhat n ω))
    (hβhat_meas : ∀ n, AEMeasurable (βhat n) P)
    (hscore : TendstoInDistribution
      (fun (n : ℕ) ω ↦ tvScore (T n ω) (δ n ω) (z n ω) β₀ / √(n : ℝ)) atTop Z (fun _ ↦ P) P')
    (hZ : HasLaw Z (gaussianReal 0 v) P')
    (hi : ContinuousAt i β₀) (hiv : i β₀ = v)
    (hinfo : ∀ η > 0, Tendsto (fun n : ℕ => P {ω | ∃ b ∈ Set.Icc (β₀ - r) (β₀ + r),
      η ≤ |tvInformation (T n ω) (δ n ω) (z n ω) b / n - i b|}) atTop (𝓝 0))
    (hr : 0 < r) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) * (βhat n ω - β₀)) atTop
      (fun ω => Z ω / (v : ℝ)) (fun _ ↦ P) P' ∧
    HasLaw (fun ω => Z ω / (v : ℝ)) (gaussianReal 0 v⁻¹) P' :=
  ⟨tendstoInDistribution_tvMPLE hv hβhat hβhat_meas hscore hi hiv hinfo hr,
    CoxAsymptotics.hasLaw_div_gaussianReal hv hZ⟩

/-- **Consistency of the normalized observed information at the time-dependent Cox estimator**:
under the hypotheses of `tendstoInMeasure_tvMPLE`, `Iₙ(βhat n) / n → v` in probability. -/
theorem tendstoInMeasure_tvInformation_tvMPLE (hv : v ≠ 0)
    (hβhat : ∀ n ω, (∃ b, IsMaxOn (tvLogPartialLikelihood₁ (T n ω) (δ n ω) (z n ω)) Set.univ b) →
      IsMaxOn (tvLogPartialLikelihood₁ (T n ω) (δ n ω) (z n ω)) Set.univ (βhat n ω))
    (hscore : TendstoInDistribution
      (fun (n : ℕ) ω ↦ tvScore (T n ω) (δ n ω) (z n ω) β₀ / √(n : ℝ)) atTop Z (fun _ ↦ P) P')
    (hi : ContinuousAt i β₀) (hiv : i β₀ = v)
    (hinfo : ∀ η > 0, Tendsto (fun n : ℕ => P {ω | ∃ b ∈ Set.Icc (β₀ - r) (β₀ + r),
      η ≤ |tvInformation (T n ω) (δ n ω) (z n ω) b / n - i b|}) atTop (𝓝 0))
    (hr : 0 < r) :
    TendstoInMeasure P (fun n ω => tvInformation (T n ω) (δ n ω) (z n ω) (βhat n ω) / n) atTop
      (fun _ => (v : ℝ)) :=
  tendstoInMeasure_info_argmax
    (fun n ω => isConcaveScore_tv (T n ω) (δ n ω) (z n ω)) hv hβhat hscore hi hiv hinfo hr

end AndersenGill

end MathlibExt.Probability.Statistics.CoxTimeVarying

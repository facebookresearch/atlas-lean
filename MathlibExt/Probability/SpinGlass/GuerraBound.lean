/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.SpinGlass.SherringtonKirkpatrick
public import Mathlib.Order.Filter.AtTopBot.Basic
import MathlibExt.Probability.Statistics.SteinLemma
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.ProductMeasure

/-!
# Guerra's replica-symmetry-breaking bound for the SK model

For every `β`, every field `h`, all admissible Parisi parameters `k, m, q` and every `N ≥ 1`, the
free energy `F_N = (1 / N) E log ∑_σ exp(H_N(σ) + h ∑_i σ_i)` of the Sherrington–Kirkpatrick
model satisfies `F_N ≤ P_k(m, q)`, where `P_k` is the Parisi functional for `ξ(x) = β² x² / 2`
(`freeEnergy_le_parisiFunctional`, Guerra's Theorem 3). Hence, for `β > 0`,
`limsup_N F_N ≤ P_k(m, q)` (`freeEnergy_le_parisiFunctional_eventually`), the upper limit being
written, as in `MathlibExt.Probability.ParisiFormulaWanted`, as "eventually
`F_N ≤ P_k(m, q) + ε` for every `ε > 0`". The conventions for `H_N`, `F_N` and `P_k` are those of
`MathlibExt.Probability.SpinGlass.SherringtonKirkpatrick`.

The proof is Guerra's interpolation. For `t ∈ [0, π / 2]` the couplings enter the Hamiltonian
with the factor `sin t` and the Gaussian fields of the Parisi levels with the factor `cos t`, and
the Parisi recursion is applied to the interpolating partition function, the couplings forming
an outermost level that is averaged plainly. At `t = π / 2` the result is `N F_N`; at `t = 0` the
sites decouple and the result is `N (log 2 + X_0)`. The recursion is studied on functions of the
field `h ∈ ℝ^{{-1, 1}^N}`: one level maps a function whose gradient lies in the probability
simplex and whose Hessian is bounded to a function of the same kind (differentiation under the
integral sign), and Gaussian integration by parts (Stein's lemma) writes its time derivative
through the gradient and Hessian of the previous level. An inequality between the time derivative
and the Hessian passes down the levels, using `m_ℓ ≤ m_{ℓ+1}` and the nonnegative comparison
matrices `(β² / 2N) (∑_i σ_i τ_i - N q_ℓ)²`, which vanish on the diagonal for `q_{k+1} = 1`. It
shows that the interpolating free energy plus `(N / 2) sin² t ∑_ℓ m_ℓ (θ(q_{ℓ+1}) - θ(q_ℓ))`
decreases on `[0, π / 2]`. This organizes Guerra's computation of the time derivative as an
induction over the levels instead of his exact formula (his sum rule).

## References

* F. Guerra, *Broken replica symmetry bounds in the mean field spin glass model*, Comm. Math.
  Phys. 233 (2003), 1–12, arXiv:cond-mat/0205123, Section 4.
-/

@[expose] public section

namespace MathlibExt.Probability.ParisiFormulaWanted.Guerra

open MeasureTheory ProbabilityTheory Real Filter Topology Metric
open MathlibExt.Probability.SherringtonKirkpatrick

noncomputable section

section PartA

variable {S : Type*} [Fintype S]

/-- The standard Gaussian measure on `Fin n → ℝ`. -/
private def stdGauss (n : ℕ) : Measure (Fin n → ℝ) := Measure.pi fun _ => gaussianReal 0 1

private instance instIsProbabilityMeasureStdGauss (n : ℕ) :
    IsProbabilityMeasure (stdGauss n) := by
  unfold stdGauss; infer_instance

/-- The field `∑_j ζ_j b_j`. -/
private def field {n : ℕ} (b : Fin n → S → ℝ) (ζ : Fin n → ℝ) : S → ℝ := fun σ => ∑ j, ζ j * b j σ

/-- Sum of absolute values. -/
private def sabs {n : ℕ} (ζ : Fin n → ℝ) : ℝ := ∑ j, |ζ j|

/-- Total size of a family of vectors. -/
private def bsize {n : ℕ} (b : Fin n → S → ℝ) : ℝ := ∑ j, ∑ σ, |b j σ|

/-- Dot product with `w` as a continuous linear functional. -/
private def dotL (w : S → ℝ) : (S → ℝ) →L[ℝ] ℝ := ∑ σ, w σ • ContinuousLinearMap.proj σ

private theorem dotL_apply (w k : S → ℝ) : dotL w k = ∑ σ, w σ * k σ := by
  simp [dotL]

/-- The joint derivative `(s, k) ↦ a s + ∑_σ w_σ k_σ`. -/
private def jointL (a : ℝ) (w : S → ℝ) : ℝ × (S → ℝ) →L[ℝ] ℝ :=
  a • ContinuousLinearMap.fst ℝ ℝ (S → ℝ) +
    ∑ σ, w σ • (ContinuousLinearMap.proj σ).comp (ContinuousLinearMap.snd ℝ ℝ (S → ℝ))

private theorem jointL_apply (a : ℝ) (w : S → ℝ) (p : ℝ × (S → ℝ)) :
    jointL a w p = a * p.1 + ∑ σ, w σ * p.2 σ := by
  simp [jointL]

private theorem sabs_nonneg {n : ℕ} (ζ : Fin n → ℝ) : 0 ≤ sabs ζ :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

private theorem bsize_nonneg {n : ℕ} (b : Fin n → S → ℝ) : 0 ≤ bsize b :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

private theorem abs_le_bsize {n : ℕ} (b : Fin n → S → ℝ) (j : Fin n) (σ : S) :
    |b j σ| ≤ bsize b := by
  unfold bsize
  calc |b j σ| ≤ ∑ τ, |b j τ| :=
        Finset.single_le_sum (f := fun τ => |b j τ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ σ)
    _ ≤ ∑ i, ∑ τ, |b i τ| :=
        Finset.single_le_sum (f := fun i => ∑ τ, |b i τ|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ j)

private theorem abs_field_le {n : ℕ} (b : Fin n → S → ℝ) (ζ : Fin n → ℝ) (σ : S) :
    |field b ζ σ| ≤ bsize b * sabs ζ := by
  unfold field sabs
  calc |∑ j, ζ j * b j σ| ≤ ∑ j, |ζ j * b j σ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, bsize b * |ζ j| := Finset.sum_le_sum fun j _ => by
        rw [abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (abs_le_bsize b j σ) (abs_nonneg _)
    _ = bsize b * ∑ j, |ζ j| := by rw [Finset.mul_sum]

private theorem norm_field_le {n : ℕ} (b : Fin n → S → ℝ) (ζ : Fin n → ℝ) :
    ‖field b ζ‖ ≤ bsize b * sabs ζ :=
  (pi_norm_le_iff_of_nonneg (mul_nonneg (bsize_nonneg b) (sabs_nonneg ζ))).2 fun σ => by
    rw [Real.norm_eq_abs]; exact abs_field_le b ζ σ

private theorem abs_le_sabs {n : ℕ} (ζ : Fin n → ℝ) (j : Fin n) : |ζ j| ≤ sabs ζ :=
  Finset.single_le_sum (f := fun i => |ζ i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)

private theorem norm_jointL_le (a : ℝ) (w : S → ℝ) : ‖jointL a w‖ ≤ |a| + ∑ σ, |w σ| := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)) fun p => ?_
  rw [jointL_apply, Real.norm_eq_abs]
  have h1 : |p.1| ≤ ‖p‖ := by simpa [Real.norm_eq_abs] using norm_fst_le p
  have h2 : ∀ σ, |p.2 σ| ≤ ‖p‖ := fun σ => by
    have := (norm_le_pi_norm p.2 σ).trans (norm_snd_le p)
    simpa [Real.norm_eq_abs] using this
  calc |a * p.1 + ∑ σ, w σ * p.2 σ| ≤ |a * p.1| + ∑ σ, |w σ * p.2 σ| :=
        (abs_add_le _ _).trans (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))
    _ ≤ |a| * ‖p‖ + ∑ σ, |w σ| * ‖p‖ := by
        rw [abs_mul]
        refine add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
          (Finset.sum_le_sum fun σ _ => ?_)
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (h2 σ) (abs_nonneg _)
    _ = (|a| + ∑ σ, |w σ|) * ‖p‖ := by rw [add_mul, Finset.sum_mul]

private theorem norm_dotL_le (w : S → ℝ) : ‖dotL w‖ ≤ ∑ σ, |w σ| := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (Finset.sum_nonneg fun _ _ => abs_nonneg _) fun k => ?_
  rw [dotL_apply, Real.norm_eq_abs]
  calc |∑ σ, w σ * k σ| ≤ ∑ σ, |w σ * k σ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ σ, |w σ| * ‖k‖ := Finset.sum_le_sum fun σ _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using norm_le_pi_norm k σ)
          (abs_nonneg _)
    _ = (∑ σ, |w σ|) * ‖k‖ := by rw [Finset.sum_mul]

/-- Regularity of the functions produced by the Parisi recursion: joint differentiability in
`(t, h)`, a gradient in the probability simplex and a bounded Hessian in `h`. -/
private structure Regular (F Ft : ℝ → (S → ℝ) → ℝ) (g : ℝ → (S → ℝ) → S → ℝ)
    (H : ℝ → (S → ℝ) → S → S → ℝ) (K B : ℝ) : Prop where
  hasFDerivAt : ∀ t h, HasFDerivAt (fun p : ℝ × (S → ℝ) => F p.1 p.2) (jointL (Ft t h) (g t h))
    (t, h)
  hess : ∀ t h σ, HasFDerivAt (fun h' => g t h' σ) (dotL (H t h σ)) h
  ft_le : ∀ t h, |Ft t h| ≤ K
  g_nonneg : ∀ t h σ, 0 ≤ g t h σ
  g_sum : ∀ t h, ∑ σ, g t h σ = 1
  H_le : ∀ t h σ τ, |H t h σ τ| ≤ B
  H_sum : ∀ t h, ∑ σ, ∑ τ, H t h σ τ = 0

namespace Regular

variable {F Ft : ℝ → (S → ℝ) → ℝ} {g : ℝ → (S → ℝ) → S → ℝ} {H : ℝ → (S → ℝ) → S → S → ℝ}
  {K B : ℝ}

private theorem g_le_one (hF : Regular F Ft g H K B) (t : ℝ) (h : S → ℝ) (σ : S) : g t h σ ≤ 1 := by
  rw [← hF.g_sum t h]
  exact Finset.single_le_sum (f := fun τ => g t h τ) (fun τ _ => hF.g_nonneg t h τ)
    (Finset.mem_univ σ)

private theorem abs_g_le_one (hF : Regular F Ft g H K B) (t : ℝ) (h : S → ℝ) (σ : S) :
    |g t h σ| ≤ 1 := by
  rw [abs_of_nonneg (hF.g_nonneg t h σ)]; exact hF.g_le_one t h σ

private theorem sum_abs_g (hF : Regular F Ft g H K B) (t : ℝ) (h : S → ℝ) :
    ∑ σ, |g t h σ| = 1 := by
  rw [← hF.g_sum t h]
  exact Finset.sum_congr rfl fun σ _ => abs_of_nonneg (hF.g_nonneg t h σ)

private theorem hasFDerivAt_h (hF : Regular F Ft g H K B) (t : ℝ) (h : S → ℝ) :
    HasFDerivAt (F t) (dotL (g t h)) h := by
  have h1 : HasFDerivAt (fun h' : S → ℝ => (t, h')) (ContinuousLinearMap.inr ℝ ℝ (S → ℝ)) h :=
    hasFDerivAt_prodMk_right t h
  have := (hF.hasFDerivAt t h).comp h h1
  have heq : (jointL (Ft t h) (g t h)).comp (ContinuousLinearMap.inr ℝ ℝ (S → ℝ)) =
      dotL (g t h) :=
    ContinuousLinearMap.ext fun k => by simp [jointL_apply, dotL_apply]
  rw [heq] at this
  exact this

private theorem hasDerivAt_t (hF : Regular F Ft g H K B) (t : ℝ) (h : S → ℝ) :
    HasDerivAt (fun s => F s h) (Ft t h) t := by
  have h1 : HasFDerivAt (fun s : ℝ => (s, h)) (ContinuousLinearMap.inl ℝ ℝ (S → ℝ)) t :=
    hasFDerivAt_prodMk_left t h
  have := ((hF.hasFDerivAt t h).comp t h1).hasDerivAt
  have heq : ((jointL (Ft t h) (g t h)).comp (ContinuousLinearMap.inl ℝ ℝ (S → ℝ))) 1 =
      Ft t h := by simp [jointL_apply]
  rw [heq] at this
  exact this

private theorem continuous (hF : Regular F Ft g H K B) :
    Continuous fun p : ℝ × (S → ℝ) => F p.1 p.2 :=
  continuous_iff_continuousAt.2 fun p => (hF.hasFDerivAt p.1 p.2).continuousAt

private theorem continuous_g (hF : Regular F Ft g H K B) (t : ℝ) (σ : S) :
    Continuous fun h => g t h σ :=
  continuous_iff_continuousAt.2 fun h => (hF.hess t h σ).continuousAt

private theorem K_nonneg [Nonempty S] (hF : Regular F Ft g H K B) : 0 ≤ K :=
  (abs_nonneg _).trans (hF.ft_le 0 (fun _ => 0))

private theorem B_nonneg [Nonempty S] (hF : Regular F Ft g H K B) : 0 ≤ B :=
  (abs_nonneg _).trans (hF.H_le 0 (fun _ => 0) (Classical.arbitrary S) (Classical.arbitrary S))

private theorem ft_eq_fderiv (hF : Regular F Ft g H K B) (t : ℝ) (h : S → ℝ) :
    Ft t h = fderiv ℝ (fun p : ℝ × (S → ℝ) => F p.1 p.2) (t, h) (1, 0) := by
  rw [(hF.hasFDerivAt t h).fderiv, jointL_apply]; simp

private theorem measurable_ft (hF : Regular F Ft g H K B) (t : ℝ) : Measurable (Ft t) := by
  have : Ft t = fun h => fderiv ℝ (fun p : ℝ × (S → ℝ) => F p.1 p.2) (t, h) (1, 0) :=
    funext fun h => hF.ft_eq_fderiv t h
  rw [this]
  exact (measurable_fderiv_apply_const ℝ _ _).comp measurable_prodMk_left

private theorem measurable_H (hF : Regular F Ft g H K B) (t : ℝ) (σ τ : S) :
    Measurable fun h => H t h σ τ := by
  classical
  have : (fun h => H t h σ τ) = fun h => fderiv ℝ (fun h' => g t h' σ) h (Pi.single τ 1) := by
    funext h
    rw [(hF.hess t h σ).fderiv, dotL_apply]
    simp [Pi.single_apply]
  rw [this]
  exact measurable_fderiv_apply_const ℝ _ _

private theorem norm_deriv_le (hF : Regular F Ft g H K B) (t : ℝ) (h : S → ℝ) :
    ‖jointL (Ft t h) (g t h)‖ ≤ K + 1 :=
  (norm_jointL_le _ _).trans (add_le_add (hF.ft_le t h) (hF.sum_abs_g t h).le)

private theorem lipschitz (hF : Regular F Ft g H K B) (p q : ℝ × (S → ℝ)) :
    |F p.1 p.2 - F q.1 q.2| ≤ (K + 1) * ‖p - q‖ := by
  have := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun p : ℝ × (S → ℝ) => F p.1 p.2) (s := Set.univ)
    (fun x _ => (hF.hasFDerivAt x.1 x.2).hasFDerivWithinAt) (fun x _ => hF.norm_deriv_le x.1 x.2)
    convex_univ (Set.mem_univ q) (Set.mem_univ p)
  simpa [Real.norm_eq_abs] using this

/-- Bound on the values met by the integrands of the level operator. -/
private theorem abs_le_of_mem_ball (hF : Regular F Ft g H K B) {n : ℕ} (b : Fin n → S → ℝ)
    {c : ℝ → ℝ} (hcb : ∀ t, |c t| ≤ 1) (p₀ p : ℝ × (S → ℝ)) (hp : p ∈ ball p₀ 1)
    (ζ : Fin n → ℝ) :
    |F p.1 (p.2 + c p.1 • field b ζ)| ≤
      |F p₀.1 p₀.2| + (K + 1) * (1 + bsize b * sabs ζ) := by
  have hK : 0 ≤ K + 1 := (norm_nonneg _).trans (hF.norm_deriv_le 0 0)
  have hl := hF.lipschitz (p.1, p.2 + c p.1 • field b ζ) p₀
  have hdist : ‖(p.1, p.2 + c p.1 • field b ζ) - p₀‖ ≤ 1 + bsize b * sabs ζ := by
    have he : (p.1, p.2 + c p.1 • field b ζ) - p₀ = (p - p₀) + (0, c p.1 • field b ζ) := by
      ext <;> simp [add_sub_right_comm]
    rw [he]
    refine (norm_add_le _ _).trans (add_le_add (le_of_lt (by simpa [dist_eq_norm] using hp)) ?_)
    rw [Prod.norm_def]
    simp only [norm_zero]
    refine max_le (mul_nonneg (bsize_nonneg b) (sabs_nonneg ζ)) ?_
    rw [norm_smul]
    calc ‖c p.1‖ * ‖field b ζ‖ ≤ 1 * (bsize b * sabs ζ) :=
          mul_le_mul (by simpa [Real.norm_eq_abs] using hcb p.1) (norm_field_le b ζ)
            (norm_nonneg _) zero_le_one
      _ = bsize b * sabs ζ := one_mul _
  have : |F p.1 (p.2 + c p.1 • field b ζ) - F p₀.1 p₀.2| ≤ (K + 1) * (1 + bsize b * sabs ζ) :=
    hl.trans (mul_le_mul_of_nonneg_left hdist hK)
  have h3 := abs_sub_abs_le_abs_sub (F p.1 (p.2 + c p.1 • field b ζ)) (F p₀.1 p₀.2)
  linarith

end Regular

/-! ### Gaussian integrability -/

private theorem integrable_exp_mul_abs (a : ℝ) :
    Integrable (fun x : ℝ => exp (a * |x|)) (gaussianReal 0 1) := by
  refine ((integrable_exp_mul_gaussianReal (μ := 0) (v := 1) |a|).add
    (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (-|a|))).mono'
    (by fun_prop) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), Pi.add_apply]
  have h1 : a * |x| ≤ |a| * |x| := mul_le_mul_of_nonneg_right (le_abs_self a) (abs_nonneg x)
  have e1 := exp_pos (|a| * x)
  have e2 := exp_pos (-|a| * x)
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx] at h1 ⊢
    have := exp_le_exp.mpr h1
    linarith
  · rw [abs_of_nonpos hx] at h1 ⊢
    have := exp_le_exp.mpr (show a * -x ≤ -|a| * x by linarith)
    linarith

private theorem integrable_exp_mul_sabs (n : ℕ) (a : ℝ) :
    Integrable (fun ζ : Fin n → ℝ => exp (a * sabs ζ)) (stdGauss n) := by
  have : (fun ζ : Fin n → ℝ => exp (a * sabs ζ)) = fun ζ => ∏ j, exp (a * |ζ j|) := by
    ext ζ; simp [sabs, Finset.mul_sum, Real.exp_sum]
  rw [this]
  exact Integrable.fintype_prod (f := fun _ x => exp (a * |x|)) fun _ => integrable_exp_mul_abs a

private theorem le_exp_sabs {n : ℕ} (ζ : Fin n → ℝ) : 1 + sabs ζ ≤ exp (sabs ζ) := by
  have := add_one_le_exp (sabs ζ); linarith

/-- Products of the polynomial weight `1 + sabs ζ` with exponential moments are integrable. -/
private theorem integrable_exp_mul_sabs_mul (n : ℕ) (a C D : ℝ) :
    Integrable (fun ζ : Fin n → ℝ => exp (a * sabs ζ) * (C + D * sabs ζ)) (stdGauss n) := by
  refine (integrable_exp_mul_sabs n (a + 1)).const_mul (|C| + |D|) |>.mono'
    (by unfold sabs; fun_prop) (ae_of_all _ fun ζ => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
  have hs := sabs_nonneg ζ
  have h1 : |C + D * sabs ζ| ≤ (|C| + |D|) * (1 + sabs ζ) := by
    calc |C + D * sabs ζ| ≤ |C| + |D| * sabs ζ := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_of_nonneg hs]
      _ ≤ (|C| + |D|) * (1 + sabs ζ) := by
          nlinarith [abs_nonneg C, abs_nonneg D]
  have h2 : exp ((a + 1) * sabs ζ) = exp (a * sabs ζ) * exp (sabs ζ) := by
    rw [← exp_add]; ring_nf
  rw [h2]
  calc exp (a * sabs ζ) * |C + D * sabs ζ| ≤ exp (a * sabs ζ) * ((|C| + |D|) * (1 + sabs ζ)) :=
        mul_le_mul_of_nonneg_left h1 (exp_pos _).le
    _ ≤ exp (a * sabs ζ) * ((|C| + |D|) * exp (sabs ζ)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_exp_sabs ζ)
          (add_nonneg (abs_nonneg _) (abs_nonneg _))) (exp_pos _).le
    _ = (|C| + |D|) * (exp (a * sabs ζ) * exp (sabs ζ)) := by ring

/-! ### Linear algebra of `jointL` under integrals -/

private theorem integral_jointL {α : Type*} [MeasurableSpace α] {μ : Measure α} (a : α → ℝ)
    (w : α → S → ℝ) (ha : Integrable a μ) (hw : ∀ σ, Integrable (fun x => w x σ) μ) :
    ∫ x, jointL (a x) (w x) ∂μ = jointL (∫ x, a x ∂μ) (fun σ => ∫ x, w x σ ∂μ) := by
  simp only [jointL]
  rw [integral_add (ha.smul_const _)
      (integrable_finsetSum _ fun τ _ => (hw τ).smul_const _),
    integral_smul_const, integral_finsetSum _ fun τ _ => (hw τ).smul_const _]
  congr 1
  exact Finset.sum_congr rfl fun τ _ => integral_smul_const _ _

private theorem aestronglyMeasurable_jointL {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (a : α → ℝ) (w : α → S → ℝ) (ha : AEStronglyMeasurable a μ)
    (hw : ∀ σ, AEStronglyMeasurable (fun x => w x σ) μ) :
    AEStronglyMeasurable (fun x => jointL (a x) (w x)) μ := by
  simp only [jointL]
  exact (ha.smul_const _).add (Finset.aestronglyMeasurable_fun_sum _ fun τ _ =>
    (hw τ).smul_const _)

omit [Fintype S] in
private theorem continuous_field {n : ℕ} (b : Fin n → S → ℝ) : Continuous (field b) :=
  continuous_pi fun _ => continuous_finsetSum _ fun j _ =>
    (continuous_apply j).mul continuous_const

omit [Fintype S] in
private theorem continuous_shift {n : ℕ} (b : Fin n → S → ℝ) (a : ℝ) (h : S → ℝ) :
    Continuous fun ζ : Fin n → ℝ => h + a • field b ζ := by
  have := continuous_field b
  fun_prop

/-! ### Differentiation under the integral sign -/

section Diff

variable {F Ft : ℝ → (S → ℝ) → ℝ} {g : ℝ → (S → ℝ) → S → ℝ} {H : ℝ → (S → ℝ) → S → S → ℝ}
  {K B : ℝ} {n : ℕ}

private theorem Regular.continuous_comp (hF : Regular F Ft g H K B) (b : Fin n → S → ℝ)
    (c : ℝ → ℝ) (t : ℝ) (h : S → ℝ) :
    Continuous fun ζ : Fin n → ℝ => F t (h + c t • field b ζ) :=
  hF.continuous.comp (continuous_const.prodMk (continuous_shift b (c t) h))

private theorem Regular.measurable_ft_comp (hF : Regular F Ft g H K B) (b : Fin n → S → ℝ)
    (c : ℝ → ℝ) (t : ℝ) (h : S → ℝ) :
    Measurable fun ζ : Fin n → ℝ => Ft t (h + c t • field b ζ) :=
  (hF.measurable_ft t).comp (continuous_shift b (c t) h).measurable

private theorem Regular.continuous_g_comp (hF : Regular F Ft g H K B) (b : Fin n → S → ℝ)
    (c : ℝ → ℝ) (t : ℝ) (h : S → ℝ) (σ : S) :
    Continuous fun ζ : Fin n → ℝ => g t (h + c t • field b ζ) σ :=
  (hF.continuous_g t σ).comp (continuous_shift b (c t) h)

private theorem Regular.measurable_H_comp (hF : Regular F Ft g H K B) (b : Fin n → S → ℝ)
    (c : ℝ → ℝ) (t : ℝ) (h : S → ℝ) (σ τ : S) :
    Measurable fun ζ : Fin n → ℝ => H t (h + c t • field b ζ) σ τ :=
  (hF.measurable_H t σ τ).comp (continuous_shift b (c t) h).measurable

/-- Chain rule for one integrand of the level operator. -/
private theorem Regular.hasFDerivAt_comp (hF : Regular F Ft g H K B) (b : Fin n → S → ℝ)
    {c c' : ℝ → ℝ} (hc : ∀ t, HasDerivAt c (c' t) t) {ψ ψ' : ℝ → ℝ}
    (hψ : ∀ x, HasDerivAt ψ (ψ' x) x) (ζ : Fin n → ℝ) (p : ℝ × (S → ℝ)) :
    HasFDerivAt (fun q : ℝ × (S → ℝ) => ψ (F q.1 (q.2 + c q.1 • field b ζ)))
      (jointL (ψ' (F p.1 (p.2 + c p.1 • field b ζ)) *
          (Ft p.1 (p.2 + c p.1 • field b ζ) +
            c' p.1 * ∑ σ, g p.1 (p.2 + c p.1 • field b ζ) σ * field b ζ σ))
        (fun σ => ψ' (F p.1 (p.2 + c p.1 • field b ζ)) * g p.1 (p.2 + c p.1 • field b ζ) σ))
      p := by
  have hc1 : HasFDerivAt (fun q : ℝ × (S → ℝ) => c q.1)
      (c' p.1 • ContinuousLinearMap.fst ℝ ℝ (S → ℝ)) p :=
    (hc p.1).comp_hasFDerivAt p hasFDerivAt_fst
  have hpath := (hasFDerivAt_fst (p := p)).prodMk
    ((hasFDerivAt_snd (p := p)).add (hc1.smul_const (field b ζ)))
  have h2 := (hF.hasFDerivAt p.1 (p.2 + c p.1 • field b ζ)).comp p hpath
  have h3 := (hψ (F p.1 (p.2 + c p.1 • field b ζ))).comp_hasFDerivAt p h2
  refine h3.congr_fderiv (ContinuousLinearMap.ext fun q => ?_)
  simp only [jointL_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst', add_apply,
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.smulRight_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  set u := ψ' (F p.1 (p.2 + c p.1 • field b ζ))
  set G := g p.1 (p.2 + c p.1 • field b ζ)
  have e : ∑ x, G x * (q.2 x + c' p.1 * q.1 * field b ζ x) =
      ∑ σ, G σ * q.2 σ + c' p.1 * q.1 * ∑ σ, G σ * field b ζ σ := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun σ _ => by ring
  have e2 : ∑ σ, u * G σ * q.2 σ = u * ∑ σ, G σ * q.2 σ := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun σ _ => by ring
  rw [e, e2]; ring

/-- **Differentiation of the level integrals.** For `F` regular and `ψ` with exponentially
bounded derivative, `(t, h) ↦ ∫ ψ(F(t, h + c(t) ∑_j ζ_j b_j)) dγ(ζ)` is differentiable. -/
private theorem Regular.hasFDerivAt_integral (hF : Regular F Ft g H K B) (b : Fin n → S → ℝ)
    {c c' : ℝ → ℝ} (hc : ∀ t, HasDerivAt c (c' t) t) (hcb : ∀ t, |c t| ≤ 1)
    (hc'b : ∀ t, |c' t| ≤ 1) {ψ ψ' : ℝ → ℝ} (hψ : ∀ x, HasDerivAt ψ (ψ' x) x)
    (hψ'c : Continuous ψ') (hψb : ∀ x, |ψ x| ≤ exp |x|) (hψ'b : ∀ x, |ψ' x| ≤ exp |x|)
    (p₀ : ℝ × (S → ℝ)) :
    HasFDerivAt (fun p : ℝ × (S → ℝ) => ∫ ζ, ψ (F p.1 (p.2 + c p.1 • field b ζ)) ∂stdGauss n)
      (jointL
        (∫ ζ, ψ' (F p₀.1 (p₀.2 + c p₀.1 • field b ζ)) *
          (Ft p₀.1 (p₀.2 + c p₀.1 • field b ζ) +
            c' p₀.1 * ∑ σ, g p₀.1 (p₀.2 + c p₀.1 • field b ζ) σ * field b ζ σ) ∂stdGauss n)
        (fun σ => ∫ ζ, ψ' (F p₀.1 (p₀.2 + c p₀.1 • field b ζ)) *
          g p₀.1 (p₀.2 + c p₀.1 • field b ζ) σ ∂stdGauss n)) p₀ := by
  have hψc : Continuous ψ := continuous_iff_continuousAt.2 fun x => (hψ x).continuousAt
  have hK : 0 ≤ K + 1 := (norm_nonneg _).trans (hF.norm_deriv_le 0 0)
  set A := |F p₀.1 p₀.2| + (K + 1) with hA
  set D := (K + 1) * bsize b with hD
  have hFb : ∀ p ∈ ball p₀ 1, ∀ ζ : Fin n → ℝ,
      |F p.1 (p.2 + c p.1 • field b ζ)| ≤ A + D * sabs ζ := fun p hp ζ => by
    have := hF.abs_le_of_mem_ball b hcb p₀ p hp ζ
    rw [hA, hD]; linarith
  let a : ℝ × (S → ℝ) → (Fin n → ℝ) → ℝ := fun p ζ =>
    ψ' (F p.1 (p.2 + c p.1 • field b ζ)) *
      (Ft p.1 (p.2 + c p.1 • field b ζ) +
        c' p.1 * ∑ σ, g p.1 (p.2 + c p.1 • field b ζ) σ * field b ζ σ)
  let w : ℝ × (S → ℝ) → (Fin n → ℝ) → S → ℝ := fun p ζ σ =>
    ψ' (F p.1 (p.2 + c p.1 • field b ζ)) * g p.1 (p.2 + c p.1 • field b ζ) σ
  have ha_meas : ∀ p, Measurable (a p) := fun p =>
    (hψ'c.comp (hF.continuous_comp b c p.1 p.2)).measurable.mul
      ((hF.measurable_ft_comp b c p.1 p.2).add (measurable_const.mul
        (Finset.measurable_fun_sum _ fun σ _ =>
          (hF.continuous_g_comp b c p.1 p.2 σ).measurable.mul
            ((continuous_apply σ).comp (continuous_field b)).measurable)))
  have hw_meas : ∀ p σ, Measurable fun ζ => w p ζ σ := fun p σ =>
    (hψ'c.comp (hF.continuous_comp b c p.1 p.2)).measurable.mul
      (hF.continuous_g_comp b c p.1 p.2 σ).measurable
  have hab : ∀ p ∈ ball p₀ 1, ∀ ζ, |a p ζ| ≤ exp (A + D * sabs ζ) * (K + bsize b * sabs ζ) :=
    fun p hp ζ => by
    have e1 : |ψ' (F p.1 (p.2 + c p.1 • field b ζ))| ≤ exp (A + D * sabs ζ) :=
      (hψ'b _).trans (exp_le_exp.2 (hFb p hp ζ))
    have e2 : |Ft p.1 (p.2 + c p.1 • field b ζ) +
        c' p.1 * ∑ σ, g p.1 (p.2 + c p.1 • field b ζ) σ * field b ζ σ| ≤
        K + bsize b * sabs ζ := by
      refine (abs_add_le _ _).trans (add_le_add (hF.ft_le _ _) ?_)
      rw [abs_mul]
      have : |∑ σ, g p.1 (p.2 + c p.1 • field b ζ) σ * field b ζ σ| ≤ bsize b * sabs ζ := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ σ, |g p.1 (p.2 + c p.1 • field b ζ) σ * field b ζ σ|
            ≤ ∑ σ, g p.1 (p.2 + c p.1 • field b ζ) σ * (bsize b * sabs ζ) :=
              Finset.sum_le_sum fun σ _ => by
                rw [abs_mul, abs_of_nonneg (hF.g_nonneg _ _ _)]
                exact mul_le_mul_of_nonneg_left (abs_field_le b ζ σ) (hF.g_nonneg _ _ _)
          _ = bsize b * sabs ζ := by rw [← Finset.sum_mul, hF.g_sum, one_mul]
      calc |c' p.1| * |∑ σ, g p.1 (p.2 + c p.1 • field b ζ) σ * field b ζ σ|
          ≤ 1 * (bsize b * sabs ζ) := mul_le_mul (hc'b _) this (abs_nonneg _) zero_le_one
        _ = bsize b * sabs ζ := one_mul _
    change |_ * _| ≤ _
    rw [abs_mul]
    exact mul_le_mul e1 e2 (abs_nonneg _) (exp_pos _).le
  have hwb : ∀ p ∈ ball p₀ 1, ∀ ζ, ∑ σ, |w p ζ σ| ≤ exp (A + D * sabs ζ) := fun p hp ζ => by
    have e1 : |ψ' (F p.1 (p.2 + c p.1 • field b ζ))| ≤ exp (A + D * sabs ζ) :=
      (hψ'b _).trans (exp_le_exp.2 (hFb p hp ζ))
    calc ∑ σ, |w p ζ σ| = |ψ' (F p.1 (p.2 + c p.1 • field b ζ))| *
          ∑ σ, |g p.1 (p.2 + c p.1 • field b ζ) σ| := by
          simp only [w, abs_mul, Finset.mul_sum]
      _ = |ψ' (F p.1 (p.2 + c p.1 • field b ζ))| := by rw [hF.sum_abs_g, mul_one]
      _ ≤ exp (A + D * sabs ζ) := e1
  have hp₀ : p₀ ∈ ball p₀ 1 := mem_ball_self one_pos
  have hbound_int : Integrable (fun ζ : Fin n → ℝ =>
      exp A * (exp (D * sabs ζ) * ((K + 1) + bsize b * sabs ζ))) (stdGauss n) :=
    (integrable_exp_mul_sabs_mul n D (K + 1) (bsize b)).const_mul _
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := stdGauss n)
    (F := fun p ζ => ψ (F p.1 (p.2 + c p.1 • field b ζ)))
    (F' := fun p ζ => jointL (a p ζ) (w p ζ)) (x₀ := p₀)
    (bound := fun ζ => exp A * (exp (D * sabs ζ) * ((K + 1) + bsize b * sabs ζ)))
    (s := ball p₀ 1) (ball_mem_nhds p₀ one_pos)
    (Eventually.of_forall fun p =>
      (hψc.comp (hF.continuous_comp b c p.1 p.2)).aestronglyMeasurable)
    (by
      refine (integrable_exp_mul_sabs n D).const_mul (exp A) |>.mono'
        (hψc.comp (hF.continuous_comp b c p₀.1 p₀.2)).aestronglyMeasurable
        (ae_of_all _ fun ζ => ?_)
      rw [Real.norm_eq_abs, ← exp_add]
      exact (hψb _).trans (exp_le_exp.2 (hFb p₀ hp₀ ζ)))
    (aestronglyMeasurable_jointL _ _ (ha_meas p₀).aestronglyMeasurable
      fun σ => (hw_meas p₀ σ).aestronglyMeasurable)
    (ae_of_all _ fun ζ p hp => by
      refine (norm_jointL_le _ _).trans ?_
      have h1 := hab p hp ζ
      have h2 := hwb p hp ζ
      have : exp (A + D * sabs ζ) = exp A * exp (D * sabs ζ) := exp_add _ _
      rw [this] at h1 h2
      nlinarith [exp_pos A, exp_pos (D * sabs ζ)])
    hbound_int
    (ae_of_all _ fun ζ p _ => hF.hasFDerivAt_comp b hc hψ ζ p)
  have ha_int : Integrable (a p₀) (stdGauss n) := by
    refine ((integrable_exp_mul_sabs_mul n D K (bsize b)).const_mul (exp A)).mono'
      (ha_meas p₀).aestronglyMeasurable (ae_of_all _ fun ζ => ?_)
    rw [Real.norm_eq_abs]
    calc |a p₀ ζ| ≤ exp (A + D * sabs ζ) * (K + bsize b * sabs ζ) := hab p₀ hp₀ ζ
      _ = exp A * (exp (D * sabs ζ) * (K + bsize b * sabs ζ)) := by rw [exp_add]; ring
  have hw_int : ∀ σ, Integrable (fun ζ => w p₀ ζ σ) (stdGauss n) := fun σ => by
    refine ((integrable_exp_mul_sabs n D).const_mul (exp A)).mono'
      (hw_meas p₀ σ).aestronglyMeasurable (ae_of_all _ fun ζ => ?_)
    rw [Real.norm_eq_abs, ← exp_add]
    refine le_trans ?_ (hwb p₀ hp₀ ζ)
    exact Finset.single_le_sum (f := fun τ => |w p₀ ζ τ|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ σ)
  rw [integral_jointL _ _ ha_int hw_int] at key
  exact key

end Diff

private theorem integral_dotL {α : Type*} [MeasurableSpace α] {μ : Measure α} (w : α → S → ℝ)
    (hw : ∀ σ, Integrable (fun x => w x σ) μ) :
    ∫ x, dotL (w x) ∂μ = dotL (fun σ => ∫ x, w x σ ∂μ) := by
  simp only [dotL]
  rw [integral_finsetSum _ fun τ _ => (hw τ).smul_const _]
  exact Finset.sum_congr rfl fun τ _ => integral_smul_const _ _

private theorem aestronglyMeasurable_dotL {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (w : α → S → ℝ) (hw : ∀ σ, AEStronglyMeasurable (fun x => w x σ) μ) :
    AEStronglyMeasurable (fun x => dotL (w x)) μ := by
  simp only [dotL]
  exact Finset.aestronglyMeasurable_fun_sum _ fun τ _ => (hw τ).smul_const _

omit [Fintype S] in
private theorem field_update {n : ℕ} (b : Fin n → S → ℝ) (x : Fin n → ℝ) (j : Fin n) (s : ℝ) :
    field b (Function.update x j s) = field b x + (s - x j) • b j := by
  ext σ
  simp only [field, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ j), Function.update_self,
    Finset.sum_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]]
  ring

section Diff2

variable {F Ft : ℝ → (S → ℝ) → ℝ} {g : ℝ → (S → ℝ) → S → ℝ} {H : ℝ → (S → ℝ) → S → S → ℝ}
  {K B : ℝ} {n : ℕ}

private theorem Regular.abs_comp_le (hF : Regular F Ft g H K B) (b : Fin n → S → ℝ) {c : ℝ → ℝ}
    (hcb : ∀ t, |c t| ≤ 1) (t : ℝ) (h : S → ℝ) (ζ : Fin n → ℝ) :
    |F t (h + c t • field b ζ)| ≤ |F t h| + (K + 1) * (1 + bsize b * sabs ζ) :=
  hF.abs_le_of_mem_ball b hcb (t, h) (t, h) (mem_ball_self one_pos) ζ

/-- **Differentiation of the weighted gradient integrals** in the field. -/
private theorem Regular.hasFDerivAt_integral_mul_g (hF : Regular F Ft g H K B) (b : Fin n → S → ℝ)
    {c : ℝ → ℝ} (hcb : ∀ t, |c t| ≤ 1) {ψ ψ' : ℝ → ℝ} (hψ : ∀ x, HasDerivAt ψ (ψ' x) x)
    (hψ'c : Continuous ψ') (hψb : ∀ x, |ψ x| ≤ exp |x|) (hψ'b : ∀ x, |ψ' x| ≤ exp |x|)
    (t : ℝ) (h₀ : S → ℝ) (σ : S) :
    HasFDerivAt (fun h : S → ℝ => ∫ ζ, ψ (F t (h + c t • field b ζ)) *
        g t (h + c t • field b ζ) σ ∂stdGauss n)
      (dotL fun τ => ∫ ζ, ψ' (F t (h₀ + c t • field b ζ)) * g t (h₀ + c t • field b ζ) τ *
          g t (h₀ + c t • field b ζ) σ +
        ψ (F t (h₀ + c t • field b ζ)) * H t (h₀ + c t • field b ζ) σ τ ∂stdGauss n) h₀ := by
  have hψc : Continuous ψ := continuous_iff_continuousAt.2 fun x => (hψ x).continuousAt
  have hB : 0 ≤ 1 + B := by
    have := (abs_nonneg _).trans (hF.H_le t h₀ σ σ); linarith
  set A := |F t h₀| + (K + 1) with hA
  set D := (K + 1) * bsize b with hD
  have hFb : ∀ h ∈ ball h₀ 1, ∀ ζ : Fin n → ℝ,
      |F t (h + c t • field b ζ)| ≤ A + D * sabs ζ := fun h hh ζ => by
    have hp : ((t, h) : ℝ × (S → ℝ)) ∈ ball (t, h₀) 1 := by
      rw [mem_ball, Prod.dist_eq, dist_self, max_lt_iff]; exact ⟨one_pos, hh⟩
    have := hF.abs_le_of_mem_ball b hcb (t, h₀) (t, h) hp ζ
    rw [hA, hD]; linarith
  let w : (S → ℝ) → (Fin n → ℝ) → S → ℝ := fun h ζ τ =>
    ψ' (F t (h + c t • field b ζ)) * g t (h + c t • field b ζ) τ * g t (h + c t • field b ζ) σ +
      ψ (F t (h + c t • field b ζ)) * H t (h + c t • field b ζ) σ τ
  have hw_meas : ∀ h τ, Measurable fun ζ => w h ζ τ := fun h τ =>
    (((hψ'c.comp (hF.continuous_comp b c t h)).mul (hF.continuous_g_comp b c t h τ)).mul
      (hF.continuous_g_comp b c t h σ)).measurable.add
      ((hψc.comp (hF.continuous_comp b c t h)).measurable.mul
        (hF.measurable_H_comp b c t h σ τ))
  have hwb : ∀ h ∈ ball h₀ 1, ∀ ζ τ, |w h ζ τ| ≤ exp (A + D * sabs ζ) * (1 + B) :=
    fun h hh ζ τ => by
    have e1 := (hψ'b (F t (h + c t • field b ζ))).trans (exp_le_exp.2 (hFb h hh ζ))
    have e2 := (hψb (F t (h + c t • field b ζ))).trans (exp_le_exp.2 (hFb h hh ζ))
    have g1 := hF.abs_g_le_one t (h + c t • field b ζ) τ
    have g2 := hF.abs_g_le_one t (h + c t • field b ζ) σ
    have hH := hF.H_le t (h + c t • field b ζ) σ τ
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_mul]
    have hE := (exp_pos (A + D * sabs ζ)).le
    calc |ψ' (F t (h + c t • field b ζ))| * |g t (h + c t • field b ζ) τ| *
          |g t (h + c t • field b ζ) σ| +
        |ψ (F t (h + c t • field b ζ))| * |H t (h + c t • field b ζ) σ τ|
        ≤ exp (A + D * sabs ζ) * 1 * 1 + exp (A + D * sabs ζ) * B := by
          gcongr
      _ = exp (A + D * sabs ζ) * (1 + B) := by ring
  have hdiff : ∀ ζ h, HasFDerivAt (fun h : S → ℝ => ψ (F t (h + c t • field b ζ)) *
      g t (h + c t • field b ζ) σ) (dotL (w h ζ)) h := fun ζ h => by
    have htr : HasFDerivAt (fun h : S → ℝ => h + c t • field b ζ)
        (ContinuousLinearMap.id ℝ (S → ℝ)) h := (hasFDerivAt_id h).add_const _
    have h1 := (hψ (F t (h + c t • field b ζ))).comp_hasFDerivAt h
      ((hF.hasFDerivAt_h t (h + c t • field b ζ)).comp h htr)
    have h2 := (hF.hess t (h + c t • field b ζ) σ).comp h htr
    have h3 := h1.mul h2
    refine h3.congr_fderiv (ContinuousLinearMap.ext fun k => ?_)
    simp only [dotL_apply, w, add_apply, smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, Function.comp_apply]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun τ _ => by ring
  have hp₀ : h₀ ∈ ball h₀ 1 := mem_ball_self one_pos
  have hw_int : ∀ τ, Integrable (fun ζ => w h₀ ζ τ) (stdGauss n) := fun τ => by
    refine ((integrable_exp_mul_sabs n D).const_mul (exp A * (1 + B))).mono'
      (hw_meas h₀ τ).aestronglyMeasurable (ae_of_all _ fun ζ => ?_)
    rw [Real.norm_eq_abs]
    refine (hwb h₀ hp₀ ζ τ).trans (le_of_eq ?_)
    rw [exp_add]; ring
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := stdGauss n)
    (F := fun h ζ => ψ (F t (h + c t • field b ζ)) * g t (h + c t • field b ζ) σ)
    (F' := fun h ζ => dotL (w h ζ)) (x₀ := h₀)
    (bound := fun ζ => Fintype.card S * (exp A * (1 + B) * exp (D * sabs ζ)))
    (s := ball h₀ 1) (ball_mem_nhds h₀ one_pos)
    (Eventually.of_forall fun h => ((hψc.comp (hF.continuous_comp b c t h)).mul
      (hF.continuous_g_comp b c t h σ)).aestronglyMeasurable)
    (by
      refine ((integrable_exp_mul_sabs n D).const_mul (exp A)).mono'
        ((hψc.comp (hF.continuous_comp b c t h₀)).mul
          (hF.continuous_g_comp b c t h₀ σ)).aestronglyMeasurable (ae_of_all _ fun ζ => ?_)
      rw [Real.norm_eq_abs, ← exp_add, abs_mul]
      calc |ψ (F t (h₀ + c t • field b ζ))| * |g t (h₀ + c t • field b ζ) σ|
          ≤ exp (A + D * sabs ζ) * 1 :=
            mul_le_mul ((hψb _).trans (exp_le_exp.2 (hFb h₀ hp₀ ζ)))
              (hF.abs_g_le_one _ _ _) (abs_nonneg _) (exp_pos _).le
        _ = exp (A + D * sabs ζ) := mul_one _)
    (aestronglyMeasurable_dotL _ fun τ => (hw_meas h₀ τ).aestronglyMeasurable)
    (ae_of_all _ fun ζ h hh => by
      refine (norm_dotL_le _).trans ?_
      calc ∑ τ, |w h ζ τ| ≤ ∑ _τ : S, exp (A + D * sabs ζ) * (1 + B) :=
            Finset.sum_le_sum fun τ _ => hwb h hh ζ τ
        _ = Fintype.card S * (exp A * (1 + B) * exp (D * sabs ζ)) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, exp_add]; ring)
    (((integrable_exp_mul_sabs n D).const_mul _).const_mul _)
    (ae_of_all _ fun ζ h _ => hdiff ζ h)
  rw [integral_dotL _ hw_int] at key
  exact key

/-- **Gaussian integration by parts** for one coordinate of the level integrand. -/
private theorem Regular.integral_ibp (hF : Regular F Ft g H K B) (b : Fin n → S → ℝ)
    {c : ℝ → ℝ} (hcb : ∀ t, |c t| ≤ 1) {ψ ψ' : ℝ → ℝ} (hψ : ∀ x, HasDerivAt ψ (ψ' x) x)
    (hψ'c : Continuous ψ') (hψb : ∀ x, |ψ x| ≤ exp |x|) (hψ'b : ∀ x, |ψ' x| ≤ exp |x|)
    (t : ℝ) (h : S → ℝ) (j : Fin n) :
    ∫ ζ, ζ j * (ψ (F t (h + c t • field b ζ)) *
        ∑ σ, g t (h + c t • field b ζ) σ * b j σ) ∂stdGauss n =
      ∫ ζ, c t * (ψ' (F t (h + c t • field b ζ)) *
          (∑ σ, g t (h + c t • field b ζ) σ * b j σ) ^ 2 +
        ψ (F t (h + c t • field b ζ)) *
          ∑ σ, ∑ τ, b j σ * H t (h + c t • field b ζ) σ τ * b j τ) ∂stdGauss n := by
  have hψc : Continuous ψ := continuous_iff_continuousAt.2 fun x => (hψ x).continuousAt
  set A := |F t h| + (K + 1) with hA
  set D := (K + 1) * bsize b with hD
  have hFb : ∀ ζ : Fin n → ℝ, |F t (h + c t • field b ζ)| ≤ A + D * sabs ζ := fun ζ => by
    have := hF.abs_comp_le b hcb t h ζ; rw [hA, hD]; linarith
  set Φ : (S → ℝ) → ℝ := fun Y => ψ (F t Y) * ∑ σ, g t Y σ * b j σ with hΦdef
  set dΦ : (S → ℝ) → ℝ := fun Y => c t * (ψ' (F t Y) * (∑ σ, g t Y σ * b j σ) ^ 2 +
    ψ (F t Y) * ∑ σ, ∑ τ, b j σ * H t Y σ τ * b j τ) with hdΦdef
  have hΦ : ∀ Y : S → ℝ, HasFDerivAt Φ
      (ψ (F t Y) • (∑ σ, b j σ • dotL (H t Y σ)) +
        (∑ σ, g t Y σ * b j σ) • (ψ' (F t Y) • dotL (g t Y))) Y := fun Y => by
    have h1 := (hψ (F t Y)).comp_hasFDerivAt Y (hF.hasFDerivAt_h t Y)
    have h2 : HasFDerivAt (fun Y => ∑ σ, g t Y σ * b j σ) (∑ σ, b j σ • dotL (H t Y σ)) Y :=
      HasFDerivAt.fun_sum fun σ _ => (hF.hess t Y σ).mul_const (b j σ)
    exact h1.mul h2
  have hpath : ∀ (x : Fin n → ℝ) (r : ℝ), h + c t • field b (Function.update x j r) =
      (h + c t • field b x) + (r - x j) • (c t • b j) := fun x r => by
    rw [field_update]
    ext σ
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hderiv : ∀ x : Fin n → ℝ, ∀ r : ℝ,
      HasDerivAt (fun r => Φ (h + c t • field b (Function.update x j r)))
        (dΦ (h + c t • field b (Function.update x j r))) r := fun x r => by
    have hP : HasDerivAt (fun r : ℝ => (h + c t • field b x) + (r - x j) • (c t • b j))
        (c t • b j) r := by
      have := ((hasDerivAt_id r).sub_const (x j)).smul_const (c t • b j)
      simpa using this.const_add (h + c t • field b x)
    have hc := (hΦ ((h + c t • field b x) + (r - x j) • (c t • b j))).comp_hasDerivAt r hP
    simp only [← hpath x] at hc
    refine hc.congr_deriv ?_
    simp only [hdΦdef, add_apply, smul_apply, FunLike.coe_sum, Finset.sum_apply,
      dotL_apply, smul_eq_mul, Pi.smul_apply]
    set Y := h + c t • field b (Function.update x j r)
    have e1 : ∑ σ, b j σ * ∑ τ, H t Y σ τ * (c t * b j τ) =
        c t * ∑ σ, ∑ τ, b j σ * H t Y σ τ * b j τ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun σ _ => by
        rw [Finset.mul_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun τ _ => by ring
    have e2 : ∑ σ, g t Y σ * (c t * b j σ) = c t * ∑ σ, g t Y σ * b j σ := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun σ _ => by ring
    rw [e1, e2]
    ring
  have hφmeas : Continuous fun ζ : Fin n → ℝ => Φ (h + c t • field b ζ) :=
    (hψc.comp (hF.continuous_comp b c t h)).mul (continuous_finsetSum _ fun σ _ =>
      (hF.continuous_g_comp b c t h σ).mul continuous_const)
  have hdφmeas : Measurable fun ζ : Fin n → ℝ => dΦ (h + c t • field b ζ) :=
    measurable_const.mul (((hψ'c.comp (hF.continuous_comp b c t h)).measurable.mul
      ((continuous_finsetSum _ fun σ _ =>
        (hF.continuous_g_comp b c t h σ).mul continuous_const).measurable.pow_const 2)).add
      ((hψc.comp (hF.continuous_comp b c t h)).measurable.mul
        (Finset.measurable_fun_sum _ fun σ _ => Finset.measurable_fun_sum _ fun τ _ =>
          (measurable_const.mul (hF.measurable_H_comp b c t h σ τ)).mul measurable_const)))
  have hgb : ∀ Y : S → ℝ, |∑ σ, g t Y σ * b j σ| ≤ bsize b := fun Y => by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ σ, |g t Y σ * b j σ| ≤ ∑ σ, g t Y σ * bsize b := Finset.sum_le_sum fun σ _ => by
          rw [abs_mul, abs_of_nonneg (hF.g_nonneg t Y σ)]
          exact mul_le_mul_of_nonneg_left (abs_le_bsize b j σ) (hF.g_nonneg t Y σ)
      _ = bsize b := by rw [← Finset.sum_mul, hF.g_sum, one_mul]
  have hHb : ∀ Y : S → ℝ, |∑ σ, ∑ τ, b j σ * H t Y σ τ * b j τ| ≤
      |B| * (Fintype.card S * Fintype.card S * bsize b ^ 2) := fun Y => by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ σ τ, |b j σ * H t Y σ τ * b j τ| ≤ |B| * bsize b ^ 2 := fun σ τ => by
      rw [abs_mul, abs_mul]
      have h1 := abs_le_bsize b j σ
      have h2 := abs_le_bsize b j τ
      have h3 := (hF.H_le t Y σ τ).trans (le_abs_self B)
      calc |b j σ| * |H t Y σ τ| * |b j τ| ≤ bsize b * |B| * bsize b :=
            mul_le_mul (mul_le_mul h1 h3 (abs_nonneg _) (bsize_nonneg b)) h2 (abs_nonneg _)
              (mul_nonneg (bsize_nonneg b) (abs_nonneg _))
        _ = |B| * bsize b ^ 2 := by ring
    calc ∑ σ, |∑ τ, b j σ * H t Y σ τ * b j τ|
        ≤ ∑ σ, ∑ τ, |b j σ * H t Y σ τ * b j τ| :=
          Finset.sum_le_sum fun σ _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _σ : S, ∑ _τ : S, |B| * bsize b ^ 2 :=
          Finset.sum_le_sum fun σ _ => Finset.sum_le_sum fun τ _ => hterm σ τ
      _ = |B| * (Fintype.card S * Fintype.card S * bsize b ^ 2) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have hdi : Integrable (fun ζ : Fin n → ℝ => dΦ (h + c t • field b ζ)) (stdGauss n) := by
    refine ((integrable_exp_mul_sabs n D).const_mul
      (exp A * (bsize b ^ 2 + |B| * (Fintype.card S * Fintype.card S * bsize b ^ 2)))).mono'
      hdφmeas.aestronglyMeasurable (ae_of_all _ fun ζ => ?_)
    rw [Real.norm_eq_abs]
    set Y := h + c t • field b ζ
    have e1 := (hψ'b (F t Y)).trans (exp_le_exp.2 (hFb ζ))
    have e2 := (hψb (F t Y)).trans (exp_le_exp.2 (hFb ζ))
    have hg2 : |(∑ σ, g t Y σ * b j σ) ^ 2| ≤ bsize b ^ 2 := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hgb Y) 2
    simp only [hdΦdef]
    rw [abs_mul]
    calc |c t| * |ψ' (F t Y) * (∑ σ, g t Y σ * b j σ) ^ 2 +
          ψ (F t Y) * ∑ σ, ∑ τ, b j σ * H t Y σ τ * b j τ|
        ≤ 1 * (exp (A + D * sabs ζ) * bsize b ^ 2 +
          exp (A + D * sabs ζ) * (|B| * (Fintype.card S * Fintype.card S * bsize b ^ 2))) := by
          refine mul_le_mul (hcb t) ((abs_add_le _ _).trans ?_) (abs_nonneg _) zero_le_one
          rw [abs_mul, abs_mul]
          exact add_le_add (mul_le_mul e1 hg2 (abs_nonneg _) (exp_pos _).le)
            (mul_le_mul e2 (hHb Y) (abs_nonneg _) (exp_pos _).le)
      _ = exp A * (bsize b ^ 2 + |B| * (Fintype.card S * Fintype.card S * bsize b ^ 2)) *
          exp (D * sabs ζ) := by rw [exp_add]; ring
  have hhi : Integrable (fun ζ : Fin n → ℝ => (ζ j - (0 : Fin n → ℝ) j) *
      Φ (h + c t • field b ζ)) (stdGauss n) := by
    refine ((integrable_exp_mul_sabs_mul n D 0 1).const_mul (exp A * bsize b)).mono'
      (((continuous_apply j).sub continuous_const).mul hφmeas).aestronglyMeasurable
      (ae_of_all _ fun ζ => ?_)
    rw [Real.norm_eq_abs]
    set Y := h + c t • field b ζ
    have e2 := (hψb (F t Y)).trans (exp_le_exp.2 (hFb ζ))
    simp only [Pi.zero_apply, sub_zero, hΦdef]
    rw [abs_mul, abs_mul]
    calc |ζ j| * (|ψ (F t Y)| * |∑ σ, g t Y σ * b j σ|)
        ≤ sabs ζ * (exp (A + D * sabs ζ) * bsize b) :=
          mul_le_mul (abs_le_sabs ζ j) (mul_le_mul e2 (hgb Y) (abs_nonneg _) (exp_pos _).le)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (sabs_nonneg ζ)
      _ = exp A * bsize b * (exp (D * sabs ζ) * (0 + 1 * sabs ζ)) := by rw [exp_add]; ring
  have key := integral_sub_mul_pi_gaussianReal (p := n) (0 : Fin n → ℝ) j
    (h := fun ζ => Φ (h + c t • field b ζ)) (dh := fun ζ => dΦ (h + c t • field b ζ))
    (ae_of_all _ fun x r => hderiv x r) hdi hhi
  simpa [stdGauss, hΦdef, hdΦdef] using key

end Diff2

end PartA

section PartB

variable {S : Type*} [Fintype S]

/-- Data of one level of the Parisi recursion: `n` Gaussian coordinates with vectors `b j`,
a parameter `m` and a time profile `c` with derivative `c'`. -/
private structure Level (S : Type*) where
  n : ℕ
  m : ℝ
  c : ℝ → ℝ
  c' : ℝ → ℝ
  b : Fin n → S → ℝ

/-- Admissible level data. -/
private structure Level.Good (L : Level S) : Prop where
  hc : ∀ t, HasDerivAt L.c (L.c' t) t
  hcb : ∀ t, |L.c t| ≤ 1
  hc'b : ∀ t, |L.c' t| ≤ 1
  m_nonneg : 0 ≤ L.m
  m_le_one : L.m ≤ 1

/-- One step of the Parisi recursion acting on functions of the time and of the field. -/
private def levelOp (L : Level S) (F : ℝ → (S → ℝ) → ℝ) (t : ℝ) (h : S → ℝ) : ℝ :=
  if L.m = 0 then ∫ ζ, F t (h + L.c t • field L.b ζ) ∂stdGauss L.n
  else 1 / L.m * Real.log (∫ ζ, Real.exp (L.m * F t (h + L.c t • field L.b ζ)) ∂stdGauss L.n)

/-- The normalizing integral of the tilted measure. -/
private def Zint (L : Level S) (F : ℝ → (S → ℝ) → ℝ) (t : ℝ) (h : S → ℝ) : ℝ :=
  ∫ ζ, exp (L.m * F t (h + L.c t • field L.b ζ)) ∂stdGauss L.n

/-- The tilted expectation. -/
private def tilt (L : Level S) (F : ℝ → (S → ℝ) → ℝ) (t : ℝ) (h : S → ℝ)
    (φ : (Fin L.n → ℝ) → ℝ) : ℝ :=
  (∫ ζ, exp (L.m * F t (h + L.c t • field L.b ζ)) * φ ζ ∂stdGauss L.n) / Zint L F t h

/-- Gradient of the output of a level. -/
private def levelG (L : Level S) (F : ℝ → (S → ℝ) → ℝ) (g : ℝ → (S → ℝ) → S → ℝ) (t : ℝ)
    (h : S → ℝ) (σ : S) : ℝ :=
  tilt L F t h fun ζ => g t (h + L.c t • field L.b ζ) σ

/-- Hessian of the output of a level. -/
private def levelH (L : Level S) (F : ℝ → (S → ℝ) → ℝ) (g : ℝ → (S → ℝ) → S → ℝ)
    (H : ℝ → (S → ℝ) → S → S → ℝ) (t : ℝ) (h : S → ℝ) (σ τ : S) : ℝ :=
  tilt L F t h (fun ζ => H t (h + L.c t • field L.b ζ) σ τ +
      L.m * g t (h + L.c t • field L.b ζ) σ * g t (h + L.c t • field L.b ζ) τ) -
    L.m * levelG L F g t h σ * levelG L F g t h τ

/-- Time derivative of the output of a level. -/
private def levelFt (L : Level S) (F Ft : ℝ → (S → ℝ) → ℝ) (g : ℝ → (S → ℝ) → S → ℝ)
    (H : ℝ → (S → ℝ) → S → S → ℝ) (t : ℝ) (h : S → ℝ) : ℝ :=
  tilt L F t h (fun ζ => Ft t (h + L.c t • field L.b ζ)) +
    L.c t * L.c' t * ∑ j, tilt L F t h fun ζ => ∑ σ, ∑ τ, L.b j σ * L.b j τ *
      (H t (h + L.c t • field L.b ζ) σ τ +
        L.m * g t (h + L.c t • field L.b ζ) σ * g t (h + L.c t • field L.b ζ) τ)

section Props

variable {F Ft : ℝ → (S → ℝ) → ℝ} {g : ℝ → (S → ℝ) → S → ℝ} {H : ℝ → (S → ℝ) → S → S → ℝ}
  {K B : ℝ}

private theorem exp_mul_le_exp_abs {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (x : ℝ) :
    exp (m * x) ≤ exp |x| := by
  refine exp_le_exp.2 ((le_abs_self _).trans ?_)
  rw [abs_mul, abs_of_nonneg hm0]
  exact mul_le_of_le_one_left (abs_nonneg _) hm1

/-- Integrability of tilted integrands with at most linear growth. -/
private theorem Regular.integrable_exp_mul (hF : Regular F Ft g H K B) (L : Level S) (hL : L.Good)
    (t : ℝ) (h : S → ℝ) {φ : (Fin L.n → ℝ) → ℝ} (hφ : AEStronglyMeasurable φ (stdGauss L.n))
    (C D' : ℝ) (hφb : ∀ ζ, |φ ζ| ≤ C + D' * sabs ζ) :
    Integrable (fun ζ => exp (L.m * F t (h + L.c t • field L.b ζ)) * φ ζ) (stdGauss L.n) := by
  set A := |F t h| + (K + 1)
  set D := (K + 1) * bsize L.b
  refine ((integrable_exp_mul_sabs_mul L.n D C D').const_mul (exp A)).mono'
    (((continuous_const.mul (hF.continuous_comp L.b L.c t h)).rexp).aestronglyMeasurable.mul hφ)
    (ae_of_all _ fun ζ => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
  have h1 : exp (L.m * F t (h + L.c t • field L.b ζ)) ≤ exp A * exp (D * sabs ζ) := by
    rw [← exp_add]
    refine (exp_mul_le_exp_abs hL.m_nonneg hL.m_le_one _).trans (exp_le_exp.2 ?_)
    have := hF.abs_comp_le L.b hL.hcb t h ζ
    simp only [A, D]; linarith
  calc exp (L.m * F t (h + L.c t • field L.b ζ)) * |φ ζ|
      ≤ exp A * exp (D * sabs ζ) * (C + D' * sabs ζ) :=
        mul_le_mul h1 (hφb ζ) (abs_nonneg _) (by positivity)
    _ = exp A * (exp (D * sabs ζ) * (C + D' * sabs ζ)) := by ring

private theorem Regular.integrable_exp (hF : Regular F Ft g H K B) (L : Level S) (hL : L.Good)
    (t : ℝ) (h : S → ℝ) :
    Integrable (fun ζ => exp (L.m * F t (h + L.c t • field L.b ζ))) (stdGauss L.n) := by
  simpa using hF.integrable_exp_mul L hL t h (φ := fun _ => (1 : ℝ)) aestronglyMeasurable_const
    1 0 (fun _ => by simp)

private theorem Regular.Zint_pos (hF : Regular F Ft g H K B) (L : Level S) (hL : L.Good)
    (t : ℝ) (h : S → ℝ) : 0 < Zint L F t h :=
  integral_exp_pos (hF.integrable_exp L hL t h)

omit [Fintype S] in
private theorem Zint_of_m_eq_zero (L : Level S) (hm : L.m = 0) (F : ℝ → (S → ℝ) → ℝ) (t : ℝ)
    (h : S → ℝ) : Zint L F t h = 1 := by
  simp [Zint, hm]

/-- Integrability of tilted bounded measurable functions. -/
private theorem Regular.integrable_exp_mul_bdd (hF : Regular F Ft g H K B) (L : Level S)
    (hL : L.Good)
    (t : ℝ) (h : S → ℝ) {φ : (Fin L.n → ℝ) → ℝ} (hφ : AEStronglyMeasurable φ (stdGauss L.n))
    (M : ℝ) (hφb : ∀ ζ, |φ ζ| ≤ M) :
    Integrable (fun ζ => exp (L.m * F t (h + L.c t • field L.b ζ)) * φ ζ) (stdGauss L.n) :=
  hF.integrable_exp_mul L hL t h hφ M 0 fun ζ => by simpa using hφb ζ

private theorem Regular.abs_tilt_le (hF : Regular F Ft g H K B) (L : Level S) (hL : L.Good)
    (t : ℝ) (h : S → ℝ) {φ : (Fin L.n → ℝ) → ℝ} (hφ : AEStronglyMeasurable φ (stdGauss L.n))
    (M : ℝ) (hφb : ∀ ζ, |φ ζ| ≤ M) : |tilt L F t h φ| ≤ M := by
  have hZ := hF.Zint_pos L hL t h
  rw [tilt, abs_div, abs_of_pos hZ, div_le_iff₀ hZ]
  refine (abs_integral_le_integral_abs).trans ?_
  rw [Zint, ← integral_const_mul]
  refine integral_mono (hF.integrable_exp_mul_bdd L hL t h hφ M hφb).abs
    ((hF.integrable_exp L hL t h).const_mul M) fun ζ => ?_
  simp only
  rw [abs_mul, abs_of_pos (exp_pos _), mul_comm M]
  exact mul_le_mul_of_nonneg_left (hφb ζ) (exp_pos _).le

private theorem Regular.tilt_mono (hF : Regular F Ft g H K B) (L : Level S) (hL : L.Good)
    (t : ℝ) (h : S → ℝ) {φ ψ : (Fin L.n → ℝ) → ℝ} (hφ : AEStronglyMeasurable φ (stdGauss L.n))
    (hψ : AEStronglyMeasurable ψ (stdGauss L.n)) (M : ℝ) (hφb : ∀ ζ, |φ ζ| ≤ M)
    (hψb : ∀ ζ, |ψ ζ| ≤ M) (hle : ∀ ζ, φ ζ ≤ ψ ζ) : tilt L F t h φ ≤ tilt L F t h ψ := by
  have hZ := hF.Zint_pos L hL t h
  rw [tilt, tilt]
  refine div_le_div_of_nonneg_right ?_ hZ.le
  exact integral_mono (hF.integrable_exp_mul_bdd L hL t h hφ M hφb)
    (hF.integrable_exp_mul_bdd L hL t h hψ M hψb) fun ζ =>
      mul_le_mul_of_nonneg_left (hle ζ) (exp_pos _).le

private theorem Regular.tilt_const (hF : Regular F Ft g H K B) (L : Level S) (hL : L.Good)
    (t : ℝ) (h : S → ℝ) (a : ℝ) : tilt L F t h (fun _ => a) = a := by
  have hZ := hF.Zint_pos L hL t h
  rw [tilt, integral_mul_const, ← Zint]
  field_simp

end Props

private theorem smul_jointL (r a : ℝ) (w : S → ℝ) :
    r • jointL a w = jointL (r * a) (fun σ => r * w σ) :=
  ContinuousLinearMap.ext fun p => by
    simp only [smul_apply, jointL_apply, smul_eq_mul, mul_add, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun σ _ => by ring

private theorem jointL_comp_inr (a : ℝ) (w : S → ℝ) :
    (jointL a w).comp (ContinuousLinearMap.inr ℝ ℝ (S → ℝ)) = dotL w :=
  ContinuousLinearMap.ext fun k => by simp [jointL_apply, dotL_apply]

section Deriv

variable {F Ft : ℝ → (S → ℝ) → ℝ} {g : ℝ → (S → ℝ) → S → ℝ} {H : ℝ → (S → ℝ) → S → S → ℝ}
  {K B : ℝ}

omit [Fintype S] in
private theorem Level.Good.hasDerivAt_exp {L : Level S} (_hL : L.Good) (x : ℝ) :
    HasDerivAt (fun x => exp (L.m * x)) (L.m * exp (L.m * x)) x := by
  have := ((hasDerivAt_id x).const_mul L.m).exp
  simpa [mul_comm] using this

omit [Fintype S] in
private theorem Level.Good.abs_exp_le {L : Level S} (hL : L.Good) (x : ℝ) :
    |exp (L.m * x)| ≤ exp |x| := by
  rw [abs_of_pos (exp_pos _)]; exact exp_mul_le_exp_abs hL.m_nonneg hL.m_le_one x

omit [Fintype S] in
private theorem Level.Good.abs_mul_exp_le {L : Level S} (hL : L.Good) (x : ℝ) :
    |L.m * exp (L.m * x)| ≤ exp |x| := by
  rw [abs_mul, abs_of_nonneg hL.m_nonneg, abs_of_pos (exp_pos _)]
  exact (mul_le_of_le_one_left (exp_pos _).le hL.m_le_one).trans
    (exp_mul_le_exp_abs hL.m_nonneg hL.m_le_one x)

private theorem Regular.abs_sum_g_mul_le (hF : Regular F Ft g H K B) {n : ℕ} (b : Fin n → S → ℝ)
    (j : Fin n) (t : ℝ) (Y : S → ℝ) : |∑ σ, g t Y σ * b j σ| ≤ bsize b := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ σ, |g t Y σ * b j σ| ≤ ∑ σ, g t Y σ * bsize b := Finset.sum_le_sum fun σ _ => by
        rw [abs_mul, abs_of_nonneg (hF.g_nonneg t Y σ)]
        exact mul_le_mul_of_nonneg_left (abs_le_bsize b j σ) (hF.g_nonneg t Y σ)
    _ = bsize b := by rw [← Finset.sum_mul, hF.g_sum, one_mul]

private theorem Regular.abs_quad_le (hF : Regular F Ft g H K B) {n : ℕ} (b : Fin n → S → ℝ)
    (j : Fin n) {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (t : ℝ) (Y : S → ℝ) :
    |∑ σ, ∑ τ, b j σ * b j τ * (H t Y σ τ + m * g t Y σ * g t Y τ)| ≤
      Fintype.card S * Fintype.card S * (bsize b ^ 2 * (|B| + 1)) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ σ τ, |b j σ * b j τ * (H t Y σ τ + m * g t Y σ * g t Y τ)| ≤
      bsize b ^ 2 * (|B| + 1) := fun σ τ => by
    rw [abs_mul, abs_mul]
    have h1 := abs_le_bsize b j σ
    have h2 := abs_le_bsize b j τ
    have h3 : |H t Y σ τ + m * g t Y σ * g t Y τ| ≤ |B| + 1 := by
      refine (abs_add_le _ _).trans (add_le_add ((hF.H_le t Y σ τ).trans (le_abs_self B)) ?_)
      rw [abs_mul, abs_mul, abs_of_nonneg hm0]
      calc m * |g t Y σ| * |g t Y τ| ≤ 1 * 1 * 1 := by
            gcongr
            · exact hF.abs_g_le_one t Y σ
            · exact hF.abs_g_le_one t Y τ
        _ = 1 := by ring
    calc |b j σ| * |b j τ| * |H t Y σ τ + m * g t Y σ * g t Y τ|
        ≤ bsize b * bsize b * (|B| + 1) :=
          mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) (bsize_nonneg b)) h3 (abs_nonneg _)
            (mul_nonneg (bsize_nonneg b) (bsize_nonneg b))
      _ = bsize b ^ 2 * (|B| + 1) := by ring
  calc ∑ σ, |∑ τ, b j σ * b j τ * (H t Y σ τ + m * g t Y σ * g t Y τ)|
      ≤ ∑ σ, ∑ τ, |b j σ * b j τ * (H t Y σ τ + m * g t Y σ * g t Y τ)| :=
        Finset.sum_le_sum fun σ _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : S, ∑ _τ : S, bsize b ^ 2 * (|B| + 1) :=
        Finset.sum_le_sum fun σ _ => Finset.sum_le_sum fun τ _ => hterm σ τ
    _ = Fintype.card S * Fintype.card S * (bsize b ^ 2 * (|B| + 1)) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

private theorem Regular.measurable_quad (hF : Regular F Ft g H K B) (L : Level S) (t : ℝ)
    (h : S → ℝ) (j : Fin L.n) :
    Measurable fun ζ : Fin L.n → ℝ => ∑ σ, ∑ τ, L.b j σ * L.b j τ *
      (H t (h + L.c t • field L.b ζ) σ τ +
        L.m * g t (h + L.c t • field L.b ζ) σ * g t (h + L.c t • field L.b ζ) τ) :=
  Finset.measurable_fun_sum _ fun σ _ => Finset.measurable_fun_sum _ fun τ _ =>
    measurable_const.mul ((hF.measurable_H_comp L.b L.c t h σ τ).add
      ((measurable_const.mul (hF.continuous_g_comp L.b L.c t h σ).measurable).mul
        (hF.continuous_g_comp L.b L.c t h τ).measurable))

/-- **The time-derivative identity**: Gaussian integration by parts turns the field term of
the time derivative into the Hessian term. -/
private theorem Regular.integral_exp_mul_ft (hF : Regular F Ft g H K B) (L : Level S) (hL : L.Good)
    (t : ℝ) (h : S → ℝ) :
    ∫ ζ, exp (L.m * F t (h + L.c t • field L.b ζ)) * (Ft t (h + L.c t • field L.b ζ) +
        L.c' t * ∑ σ, g t (h + L.c t • field L.b ζ) σ * field L.b ζ σ) ∂stdGauss L.n =
      ∫ ζ, exp (L.m * F t (h + L.c t • field L.b ζ)) * Ft t (h + L.c t • field L.b ζ)
          ∂stdGauss L.n +
        L.c t * L.c' t * ∑ j, ∫ ζ, exp (L.m * F t (h + L.c t • field L.b ζ)) *
          ∑ σ, ∑ τ, L.b j σ * L.b j τ * (H t (h + L.c t • field L.b ζ) σ τ +
            L.m * g t (h + L.c t • field L.b ζ) σ * g t (h + L.c t • field L.b ζ) τ)
          ∂stdGauss L.n := by
  have hpt : ∀ ζ : Fin L.n → ℝ, exp (L.m * F t (h + L.c t • field L.b ζ)) *
      (Ft t (h + L.c t • field L.b ζ) +
        L.c' t * ∑ σ, g t (h + L.c t • field L.b ζ) σ * field L.b ζ σ) =
      exp (L.m * F t (h + L.c t • field L.b ζ)) * Ft t (h + L.c t • field L.b ζ) +
        L.c' t * ∑ j, ζ j * (exp (L.m * F t (h + L.c t • field L.b ζ)) *
          ∑ σ, g t (h + L.c t • field L.b ζ) σ * L.b j σ) := fun ζ => by
    have e : ∑ σ, g t (h + L.c t • field L.b ζ) σ * field L.b ζ σ =
        ∑ j, ζ j * ∑ σ, g t (h + L.c t • field L.b ζ) σ * L.b j σ := by
      simp only [field, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun σ _ => by ring
    rw [e, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  have hint1 : Integrable (fun ζ => exp (L.m * F t (h + L.c t • field L.b ζ)) *
      Ft t (h + L.c t • field L.b ζ)) (stdGauss L.n) :=
    hF.integrable_exp_mul_bdd L hL t h (hF.measurable_ft_comp L.b L.c t h).aestronglyMeasurable
      K fun ζ => hF.ft_le _ _
  have hint2 : ∀ j, Integrable (fun ζ : Fin L.n → ℝ => ζ j *
      (exp (L.m * F t (h + L.c t • field L.b ζ)) *
        ∑ σ, g t (h + L.c t • field L.b ζ) σ * L.b j σ)) (stdGauss L.n) := fun j => by
    have := hF.integrable_exp_mul L hL t h
      (φ := fun ζ => ζ j * ∑ σ, g t (h + L.c t • field L.b ζ) σ * L.b j σ)
      (((continuous_apply j).mul (continuous_finsetSum _ fun σ _ =>
        (hF.continuous_g_comp L.b L.c t h σ).mul continuous_const))).aestronglyMeasurable
      0 (bsize L.b) fun ζ => by
        rw [abs_mul, zero_add, mul_comm (bsize L.b)]
        exact mul_le_mul (abs_le_sabs ζ j) (hF.abs_sum_g_mul_le L.b j t _) (abs_nonneg _)
          (sabs_nonneg ζ)
    refine this.congr (ae_of_all _ fun ζ => ?_)
    simp only; ring
  have hibp : ∀ j, ∫ ζ : Fin L.n → ℝ, ζ j * (exp (L.m * F t (h + L.c t • field L.b ζ)) *
      ∑ σ, g t (h + L.c t • field L.b ζ) σ * L.b j σ) ∂stdGauss L.n =
      L.c t * ∫ ζ, exp (L.m * F t (h + L.c t • field L.b ζ)) *
          ∑ σ, ∑ τ, L.b j σ * L.b j τ * (H t (h + L.c t • field L.b ζ) σ τ +
            L.m * g t (h + L.c t • field L.b ζ) σ * g t (h + L.c t • field L.b ζ) τ)
          ∂stdGauss L.n := fun j => by
    rw [hF.integral_ibp L.b hL.hcb (ψ := fun x => exp (L.m * x))
      (ψ' := fun x => L.m * exp (L.m * x)) hL.hasDerivAt_exp (by fun_prop) hL.abs_exp_le
      hL.abs_mul_exp_le t h j, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun ζ => ?_)
    simp only
    congr 1
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun τ _ => by ring
  rw [integral_congr_ae (ae_of_all _ hpt), integral_add hint1
      ((integrable_finsetSum _ fun j _ => hint2 j).const_mul _),
    integral_const_mul, integral_finsetSum _ fun j _ => hint2 j]
  simp only [hibp]
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

end Deriv

section Deriv2

variable {F Ft : ℝ → (S → ℝ) → ℝ} {g : ℝ → (S → ℝ) → S → ℝ} {H : ℝ → (S → ℝ) → S → S → ℝ}
  {K B : ℝ}

private theorem abs_id_le_exp_abs (x : ℝ) : |id x| ≤ exp |x| := by
  have := add_one_le_exp |x|; simp only [id]; linarith

private theorem abs_one_le_exp_abs (x : ℝ) : |(fun _ : ℝ => (1 : ℝ)) x| ≤ exp |x| := by
  simp [one_le_exp (abs_nonneg x)]

/-- **Joint derivative of a level.** -/
private theorem Regular.hasFDerivAt_levelOp (hF : Regular F Ft g H K B) (L : Level S) (hL : L.Good)
    (t : ℝ) (h : S → ℝ) :
    HasFDerivAt (fun p : ℝ × (S → ℝ) => levelOp L F p.1 p.2)
      (jointL (levelFt L F Ft g H t h) (levelG L F g t h)) (t, h) := by
  have hA : HasFDerivAt (fun p : ℝ × (S → ℝ) => levelOp L F p.1 p.2)
      (jointL ((∫ ζ, exp (L.m * F t (h + L.c t • field L.b ζ)) *
          (Ft t (h + L.c t • field L.b ζ) +
            L.c' t * ∑ σ, g t (h + L.c t • field L.b ζ) σ * field L.b ζ σ) ∂stdGauss L.n) /
          Zint L F t h) (levelG L F g t h)) (t, h) := by
    by_cases hm : L.m = 0
    · have hfun : (fun p : ℝ × (S → ℝ) => levelOp L F p.1 p.2) =
          fun p => ∫ ζ, id (F p.1 (p.2 + L.c p.1 • field L.b ζ)) ∂stdGauss L.n :=
        funext fun p => by simp [levelOp, hm]
      rw [hfun]
      have key := hF.hasFDerivAt_integral L.b hL.hc hL.hcb hL.hc'b (ψ := id)
        (ψ' := fun _ => 1) (fun x => hasDerivAt_id x) continuous_const abs_id_le_exp_abs
        abs_one_le_exp_abs (t, h)
      refine key.congr_fderiv ?_
      have hZ1 := Zint_of_m_eq_zero L hm F t h
      congr 1
      · simp [hZ1, hm]
      · funext σ
        simp [levelG, tilt, hZ1, hm]
    · have hfun : (fun p : ℝ × (S → ℝ) => levelOp L F p.1 p.2) =
          fun p => 1 / L.m * Real.log
            (∫ ζ, exp (L.m * F p.1 (p.2 + L.c p.1 • field L.b ζ)) ∂stdGauss L.n) :=
        funext fun p => by simp [levelOp, hm]
      rw [hfun]
      have hZ := hF.hasFDerivAt_integral L.b hL.hc hL.hcb hL.hc'b
        (ψ := fun x => exp (L.m * x)) (ψ' := fun x => L.m * exp (L.m * x))
        hL.hasDerivAt_exp (by fun_prop) hL.abs_exp_le hL.abs_mul_exp_le (t, h)
      have hlog := (hZ.log (hF.Zint_pos L hL t h).ne').const_mul (1 / L.m)
      refine hlog.congr_fderiv ?_
      rw [smul_jointL, smul_jointL]
      have e1 : ∀ φ : (Fin L.n → ℝ) → ℝ, ∫ ζ, L.m * exp (L.m * F t (h + L.c t • field L.b ζ)) *
          φ ζ ∂stdGauss L.n =
          L.m * ∫ ζ, exp (L.m * F t (h + L.c t • field L.b ζ)) * φ ζ ∂stdGauss L.n :=
        fun φ => by
          rw [← integral_const_mul]
          exact integral_congr_ae (ae_of_all _ fun ζ => by simp only; ring)
      have hZ0 := (hF.Zint_pos L hL t h).ne'
      congr 1
      · simp only [e1]
        rw [show (∫ ζ, exp (L.m * F t (h + L.c t • field L.b ζ)) ∂stdGauss L.n) =
          Zint L F t h from rfl]
        field_simp
      · funext σ
        simp only [e1, levelG, tilt]
        rw [show (∫ ζ, exp (L.m * F t (h + L.c t • field L.b ζ)) ∂stdGauss L.n) =
          Zint L F t h from rfl]
        field_simp
  have hB : (∫ ζ, exp (L.m * F t (h + L.c t • field L.b ζ)) *
      (Ft t (h + L.c t • field L.b ζ) +
        L.c' t * ∑ σ, g t (h + L.c t • field L.b ζ) σ * field L.b ζ σ) ∂stdGauss L.n) /
      Zint L F t h = levelFt L F Ft g H t h := by
    rw [hF.integral_exp_mul_ft L hL t h, levelFt, tilt, add_div, Finset.mul_sum,
      Finset.mul_sum, Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [tilt]; ring
  rw [← hB]; exact hA

/-- **Hessian of a level.** -/
private theorem Regular.hasFDerivAt_levelG (hF : Regular F Ft g H K B) (L : Level S) (hL : L.Good)
    (t : ℝ) (h : S → ℝ) (σ : S) :
    HasFDerivAt (fun h' => levelG L F g t h' σ) (dotL (levelH L F g H t h σ)) h := by
  have hN := hF.hasFDerivAt_integral_mul_g L.b hL.hcb (ψ := fun x => exp (L.m * x))
    (ψ' := fun x => L.m * exp (L.m * x)) hL.hasDerivAt_exp (by fun_prop) hL.abs_exp_le
    hL.abs_mul_exp_le t h σ
  have hZj := hF.hasFDerivAt_integral L.b hL.hc hL.hcb hL.hc'b
    (ψ := fun x => exp (L.m * x)) (ψ' := fun x => L.m * exp (L.m * x))
    hL.hasDerivAt_exp (by fun_prop) hL.abs_exp_le hL.abs_mul_exp_le (t, h)
  have hZ := hZj.comp h (hasFDerivAt_prodMk_right t h)
  rw [jointL_comp_inr] at hZ
  have hZpos := hF.Zint_pos L hL t h
  have hZinv := (hasDerivAt_inv hZpos.ne').comp_hasFDerivAt h hZ
  have hprod := hN.mul hZinv
  have hfun : (fun h' => levelG L F g t h' σ) = fun h' =>
      (∫ ζ, exp (L.m * F t (h' + L.c t • field L.b ζ)) * g t (h' + L.c t • field L.b ζ) σ
        ∂stdGauss L.n) * (∫ ζ, exp (L.m * F t (h' + L.c t • field L.b ζ)) ∂stdGauss L.n)⁻¹ :=
    funext fun h' => by simp [levelG, tilt, Zint, div_eq_mul_inv]
  rw [hfun]
  refine hprod.congr_fderiv (ContinuousLinearMap.ext fun k => ?_)
  have e1 : ∀ τ, ∫ ζ, L.m * exp (L.m * F t (h + L.c t • field L.b ζ)) *
      g t (h + L.c t • field L.b ζ) τ ∂stdGauss L.n =
      L.m * ∫ ζ, exp (L.m * F t (h + L.c t • field L.b ζ)) * g t (h + L.c t • field L.b ζ) τ
        ∂stdGauss L.n := fun τ => by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun ζ => by simp only; ring)
  have e2 : ∀ τ, ∫ ζ, L.m * exp (L.m * F t (h + L.c t • field L.b ζ)) *
      g t (h + L.c t • field L.b ζ) τ * g t (h + L.c t • field L.b ζ) σ +
      exp (L.m * F t (h + L.c t • field L.b ζ)) * H t (h + L.c t • field L.b ζ) σ τ
        ∂stdGauss L.n =
      ∫ ζ, exp (L.m * F t (h + L.c t • field L.b ζ)) * (H t (h + L.c t • field L.b ζ) σ τ +
        L.m * g t (h + L.c t • field L.b ζ) σ * g t (h + L.c t • field L.b ζ) τ)
        ∂stdGauss L.n := fun τ =>
    integral_congr_ae (ae_of_all _ fun ζ => by simp only; ring)
  simp only [add_apply, smul_apply, dotL_apply, smul_eq_mul, e1, e2, Function.comp_apply]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [levelH, levelG, tilt]
  field_simp
  ring

end Deriv2

section Linear

variable {F Ft : ℝ → (S → ℝ) → ℝ} {g : ℝ → (S → ℝ) → S → ℝ} {H : ℝ → (S → ℝ) → S → S → ℝ}
  {K B : ℝ}

/-- Integrability against the tilt. -/
private def TInt (L : Level S) (F : ℝ → (S → ℝ) → ℝ) (t : ℝ) (h : S → ℝ) (φ : (Fin L.n → ℝ) → ℝ) :
    Prop :=
  Integrable (fun ζ => exp (L.m * F t (h + L.c t • field L.b ζ)) * φ ζ) (stdGauss L.n)

omit [Fintype S] in
private theorem tilt_add (L : Level S) (F : ℝ → (S → ℝ) → ℝ) (t : ℝ) (h : S → ℝ)
    {φ ψ : (Fin L.n → ℝ) → ℝ} (hφ : TInt L F t h φ) (hψ : TInt L F t h ψ) :
    tilt L F t h (fun ζ => φ ζ + ψ ζ) = tilt L F t h φ + tilt L F t h ψ := by
  simp only [tilt, mul_add]
  rw [integral_add hφ hψ, add_div]

omit [Fintype S] in
private theorem tilt_const_mul (L : Level S) (F : ℝ → (S → ℝ) → ℝ) (t : ℝ) (h : S → ℝ) (a : ℝ)
    (φ : (Fin L.n → ℝ) → ℝ) :
    tilt L F t h (fun ζ => a * φ ζ) = a * tilt L F t h φ := by
  simp only [tilt]
  rw [← mul_div_assoc, ← integral_const_mul]
  congr 1
  exact integral_congr_ae (ae_of_all _ fun ζ => by simp only; ring)

omit [Fintype S] in
private theorem tilt_sum (L : Level S) (F : ℝ → (S → ℝ) → ℝ) (t : ℝ) (h : S → ℝ) {ι : Type*}
    (s : Finset ι) (φ : ι → (Fin L.n → ℝ) → ℝ) (hφ : ∀ i ∈ s, TInt L F t h (φ i)) :
    tilt L F t h (fun ζ => ∑ i ∈ s, φ i ζ) = ∑ i ∈ s, tilt L F t h (φ i) := by
  simp only [tilt, Finset.mul_sum]
  rw [integral_finsetSum _ hφ, Finset.sum_div]

omit [Fintype S] in
private theorem TInt.add {L : Level S} {F : ℝ → (S → ℝ) → ℝ} {t : ℝ} {h : S → ℝ}
    {φ ψ : (Fin L.n → ℝ) → ℝ} (hφ : TInt L F t h φ) (hψ : TInt L F t h ψ) :
    TInt L F t h (fun ζ => φ ζ + ψ ζ) := by
  unfold TInt at *
  refine (hφ.add hψ).congr (ae_of_all _ fun ζ => ?_)
  simp only [Pi.add_apply]; ring

omit [Fintype S] in
private theorem TInt.const_mul {L : Level S} {F : ℝ → (S → ℝ) → ℝ} {t : ℝ} {h : S → ℝ}
    {φ : (Fin L.n → ℝ) → ℝ} (hφ : TInt L F t h φ) (a : ℝ) :
    TInt L F t h (fun ζ => a * φ ζ) := by
  unfold TInt at *
  refine (hφ.const_mul a).congr (ae_of_all _ fun ζ => ?_)
  simp only; ring

omit [Fintype S] in
private theorem TInt.sum {L : Level S} {F : ℝ → (S → ℝ) → ℝ} {t : ℝ} {h : S → ℝ} {ι : Type*}
    (s : Finset ι) {φ : ι → (Fin L.n → ℝ) → ℝ} (hφ : ∀ i ∈ s, TInt L F t h (φ i)) :
    TInt L F t h (fun ζ => ∑ i ∈ s, φ i ζ) := by
  unfold TInt at *
  simpa [Finset.mul_sum] using integrable_finsetSum s hφ

private theorem Regular.tInt_bdd (hF : Regular F Ft g H K B) (L : Level S) (hL : L.Good) (t : ℝ)
    (h : S → ℝ) {φ : (Fin L.n → ℝ) → ℝ} (hφ : Measurable φ) (M : ℝ) (hφb : ∀ ζ, |φ ζ| ≤ M) :
    TInt L F t h φ :=
  hF.integrable_exp_mul_bdd L hL t h hφ.aestronglyMeasurable M hφb

private theorem Regular.tilt_mono' (hF : Regular F Ft g H K B) (L : Level S) (hL : L.Good) (t : ℝ)
    (h : S → ℝ) {φ ψ : (Fin L.n → ℝ) → ℝ} (hφ : TInt L F t h φ) (hψ : TInt L F t h ψ)
    (hle : ∀ ζ, φ ζ ≤ ψ ζ) : tilt L F t h φ ≤ tilt L F t h ψ := by
  rw [tilt, tilt]
  exact div_le_div_of_nonneg_right (integral_mono hφ hψ fun ζ =>
    mul_le_mul_of_nonneg_left (hle ζ) (exp_pos _).le) (hF.Zint_pos L hL t h).le

private theorem Regular.tilt_nonneg (hF : Regular F Ft g H K B) (L : Level S) (hL : L.Good) (t : ℝ)
    (h : S → ℝ) {φ : (Fin L.n → ℝ) → ℝ} (hφ : ∀ ζ, 0 ≤ φ ζ) : 0 ≤ tilt L F t h φ :=
  div_nonneg (integral_nonneg fun ζ => mul_nonneg (exp_pos _).le (hφ ζ))
    (hF.Zint_pos L hL t h).le

end Linear

section RegularLevel

variable {F Ft : ℝ → (S → ℝ) → ℝ} {g : ℝ → (S → ℝ) → S → ℝ} {H : ℝ → (S → ℝ) → S → S → ℝ}
  {K B : ℝ}

private theorem Regular.tInt_g (hF : Regular F Ft g H K B) (L : Level S) (hL : L.Good) (t : ℝ)
    (h : S → ℝ) (σ : S) : TInt L F t h fun ζ => g t (h + L.c t • field L.b ζ) σ :=
  hF.tInt_bdd L hL t h (hF.continuous_g_comp L.b L.c t h σ).measurable 1
    fun _ => hF.abs_g_le_one _ _ _

private theorem Regular.measurable_M (hF : Regular F Ft g H K B) (L : Level S) (t : ℝ) (h : S → ℝ)
    (σ τ : S) : Measurable fun ζ : Fin L.n → ℝ => H t (h + L.c t • field L.b ζ) σ τ +
      L.m * g t (h + L.c t • field L.b ζ) σ * g t (h + L.c t • field L.b ζ) τ :=
  (hF.measurable_H_comp L.b L.c t h σ τ).add
    ((measurable_const.mul (hF.continuous_g_comp L.b L.c t h σ).measurable).mul
      (hF.continuous_g_comp L.b L.c t h τ).measurable)

private theorem Regular.abs_M_le (hF : Regular F Ft g H K B) {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (t : ℝ) (Y : S → ℝ) (σ τ : S) : |H t Y σ τ + m * g t Y σ * g t Y τ| ≤ |B| + 1 := by
  refine (abs_add_le _ _).trans (add_le_add ((hF.H_le t Y σ τ).trans (le_abs_self B)) ?_)
  rw [abs_mul, abs_mul, abs_of_nonneg hm0]
  calc m * |g t Y σ| * |g t Y τ| ≤ 1 * 1 * 1 := by
        gcongr
        · exact hF.abs_g_le_one t Y σ
        · exact hF.abs_g_le_one t Y τ
    _ = 1 := by ring

private theorem Regular.tInt_M (hF : Regular F Ft g H K B) (L : Level S) (hL : L.Good) (t : ℝ)
    (h : S → ℝ) (σ τ : S) : TInt L F t h fun ζ => H t (h + L.c t • field L.b ζ) σ τ +
      L.m * g t (h + L.c t • field L.b ζ) σ * g t (h + L.c t • field L.b ζ) τ :=
  hF.tInt_bdd L hL t h (hF.measurable_M L t h σ τ) (|B| + 1)
    fun _ => hF.abs_M_le hL.m_nonneg hL.m_le_one t _ σ τ

private theorem Regular.tInt_ft (hF : Regular F Ft g H K B) (L : Level S) (hL : L.Good) (t : ℝ)
    (h : S → ℝ) : TInt L F t h fun ζ => Ft t (h + L.c t • field L.b ζ) :=
  hF.tInt_bdd L hL t h (hF.measurable_ft_comp L.b L.c t h) K fun _ => hF.ft_le _ _

private theorem Regular.levelG_nonneg (hF : Regular F Ft g H K B) (L : Level S) (hL : L.Good)
    (t : ℝ) (h : S → ℝ) (σ : S) : 0 ≤ levelG L F g t h σ :=
  hF.tilt_nonneg L hL t h fun _ => hF.g_nonneg _ _ _

private theorem Regular.levelG_sum (hF : Regular F Ft g H K B) (L : Level S) (hL : L.Good)
    (t : ℝ) (h : S → ℝ) : ∑ σ, levelG L F g t h σ = 1 := by
  unfold levelG
  rw [← tilt_sum L F t h _ _ fun σ _ => hF.tInt_g L hL t h σ]
  simp only [hF.g_sum]
  exact hF.tilt_const L hL t h 1

private theorem Regular.abs_levelG_le (hF : Regular F Ft g H K B) (L : Level S) (hL : L.Good)
    (t : ℝ) (h : S → ℝ) (σ : S) : |levelG L F g t h σ| ≤ 1 :=
  hF.abs_tilt_le L hL t h (hF.continuous_g_comp L.b L.c t h σ).aestronglyMeasurable 1
    fun _ => hF.abs_g_le_one _ _ _

/-- **One level of the Parisi recursion preserves regularity.** -/
private theorem Regular.levelOp (hF : Regular F Ft g H K B) (L : Level S) (hL : L.Good) :
    Regular (levelOp L F) (levelFt L F Ft g H) (levelG L F g) (levelH L F g H)
      (K + L.n * (Fintype.card S * Fintype.card S * (bsize L.b ^ 2 * (|B| + 1)))) (|B| + 2) where
  hasFDerivAt t h := hF.hasFDerivAt_levelOp L hL t h
  hess t h σ := hF.hasFDerivAt_levelG L hL t h σ
  ft_le t h := by
    unfold levelFt
    have h1 : |tilt L F t h fun ζ => Ft t (h + L.c t • field L.b ζ)| ≤ K :=
      hF.abs_tilt_le L hL t h (hF.measurable_ft_comp L.b L.c t h).aestronglyMeasurable K
        fun ζ => hF.ft_le _ _
    have h2 : ∀ j, |tilt L F t h fun ζ => ∑ σ, ∑ τ, L.b j σ * L.b j τ *
        (H t (h + L.c t • field L.b ζ) σ τ +
          L.m * g t (h + L.c t • field L.b ζ) σ * g t (h + L.c t • field L.b ζ) τ)| ≤
        Fintype.card S * Fintype.card S * (bsize L.b ^ 2 * (|B| + 1)) := fun j =>
      hF.abs_tilt_le L hL t h (hF.measurable_quad L t h j).aestronglyMeasurable _
        fun ζ => hF.abs_quad_le L.b j hL.m_nonneg hL.m_le_one t _
    have hcc : |L.c t * L.c' t| ≤ 1 := by
      rw [abs_mul]
      calc |L.c t| * |L.c' t| ≤ 1 * 1 :=
            mul_le_mul (hL.hcb t) (hL.hc'b t) (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    refine (abs_add_le _ _).trans (add_le_add h1 ?_)
    rw [abs_mul]
    refine (mul_le_of_le_one_left (abs_nonneg _) hcc).trans ?_
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j, |tilt L F t h fun ζ => ∑ σ, ∑ τ, L.b j σ * L.b j τ *
          (H t (h + L.c t • field L.b ζ) σ τ +
            L.m * g t (h + L.c t • field L.b ζ) σ * g t (h + L.c t • field L.b ζ) τ)|
        ≤ ∑ _j : Fin L.n, Fintype.card S * Fintype.card S * (bsize L.b ^ 2 * (|B| + 1)) :=
          Finset.sum_le_sum fun j _ => h2 j
      _ = L.n * (Fintype.card S * Fintype.card S * (bsize L.b ^ 2 * (|B| + 1))) := by
          simp
  g_nonneg t h σ := hF.levelG_nonneg L hL t h σ
  g_sum t h := hF.levelG_sum L hL t h
  H_le t h σ τ := by
    unfold levelH
    have h1 := hF.abs_tilt_le L hL t h (hF.measurable_M L t h σ τ).aestronglyMeasurable
      (|B| + 1) fun ζ => hF.abs_M_le hL.m_nonneg hL.m_le_one t _ σ τ
    have h2 : |L.m * levelG L F g t h σ * levelG L F g t h τ| ≤ 1 := by
      rw [abs_mul, abs_mul, abs_of_nonneg hL.m_nonneg]
      calc L.m * |levelG L F g t h σ| * |levelG L F g t h τ| ≤ 1 * 1 * 1 :=
            mul_le_mul (mul_le_mul hL.m_le_one (hF.abs_levelG_le L hL t h σ) (abs_nonneg _)
              zero_le_one) (hF.abs_levelG_le L hL t h τ) (abs_nonneg _) (by norm_num)
        _ = 1 := by ring
    calc |_ - _| ≤ |_| + |_| := abs_sub _ _
      _ ≤ (|B| + 1) + 1 := add_le_add h1 h2
      _ = |B| + 2 := by ring
  H_sum t h := by
    unfold levelH
    simp only [Finset.sum_sub_distrib]
    rw [← Finset.sum_congr rfl fun σ _ => (tilt_sum L F t h Finset.univ _
        fun τ _ => hF.tInt_M L hL t h σ τ),
      ← tilt_sum L F t h Finset.univ _ fun σ _ => TInt.sum _ fun τ _ => hF.tInt_M L hL t h σ τ]
    have hpt : ∀ ζ : Fin L.n → ℝ, ∑ σ, ∑ τ, (H t (h + L.c t • field L.b ζ) σ τ +
        L.m * g t (h + L.c t • field L.b ζ) σ * g t (h + L.c t • field L.b ζ) τ) = L.m := by
      intro ζ
      simp only [Finset.sum_add_distrib, hF.H_sum, zero_add]
      simp only [mul_assoc, ← Finset.mul_sum, hF.g_sum, mul_one]
    simp only [hpt, hF.tilt_const L hL t h]
    have : ∑ σ, ∑ τ, L.m * levelG L F g t h σ * levelG L F g t h τ = L.m := by
      simp only [mul_assoc, ← Finset.mul_sum, hF.levelG_sum L hL t h, mul_one]
    rw [this, sub_self]

end RegularLevel

section Claim

variable {F Ft : ℝ → (S → ℝ) → ℝ} {g : ℝ → (S → ℝ) → S → ℝ} {H : ℝ → (S → ℝ) → S → S → ℝ}
  {K B : ℝ}

/-- **Propagation of Guerra's inequality through one level.** -/
private theorem Regular.levelFt_le (hF : Regular F Ft g H K B) (L : Level S) (hL : L.Good)
    (E E' : S → S → ℝ) (m' δ cst s t : ℝ) (hs : 0 ≤ s) (hm : L.m ≤ m')
    (hE' : ∀ σ τ, 0 ≤ E' σ τ)
    (hcov : ∀ σ τ, L.c t * L.c' t * ∑ j, L.b j σ * L.b j τ = s * (E' σ τ - E σ τ - δ))
    (hclaim : ∀ h, Ft t h ≤
      -(s * (∑ σ, ∑ τ, E' σ τ * (H t h σ τ + m' * g t h σ * g t h τ) + cst)))
    (h : S → ℝ) :
    levelFt L F Ft g H t h ≤ -(s * (∑ σ, ∑ τ, E σ τ * (levelH L F g H t h σ τ +
      L.m * levelG L F g t h σ * levelG L F g t h τ) + (cst + δ * L.m))) := by
  set M : (Fin L.n → ℝ) → S → S → ℝ := fun ζ σ τ => H t (h + L.c t • field L.b ζ) σ τ +
    L.m * g t (h + L.c t • field L.b ζ) σ * g t (h + L.c t • field L.b ζ) τ with hMdef
  have hM : ∀ σ τ, TInt L F t h fun ζ => M ζ σ τ := fun σ τ => hF.tInt_M L hL t h σ τ
  have hMM : TInt L F t h fun ζ => ∑ σ, ∑ τ, s * (E' σ τ - E σ τ - δ) * M ζ σ τ :=
    TInt.sum _ fun σ _ => TInt.sum _ fun τ _ => (hM σ τ).const_mul _
  -- the field term of the time derivative, rewritten with the covariance identity
  have hpt : ∀ ζ, L.c t * L.c' t * ∑ j, ∑ σ, ∑ τ, L.b j σ * L.b j τ * M ζ σ τ =
      ∑ σ, ∑ τ, s * (E' σ τ - E σ τ - δ) * M ζ σ τ := fun ζ => by
    simp only [← hcov, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun j _ => by ring
  have h1 : levelFt L F Ft g H t h = tilt L F t h (fun ζ => Ft t (h + L.c t • field L.b ζ) +
      ∑ σ, ∑ τ, s * (E' σ τ - E σ τ - δ) * M ζ σ τ) := by
    rw [tilt_add L F t h (hF.tInt_ft L hL t h) hMM]
    unfold levelFt
    congr 1
    rw [← tilt_sum L F t h _ _ fun j _ => TInt.sum _ fun σ _ => TInt.sum _ fun τ _ =>
      (hM σ τ).const_mul _, ← tilt_const_mul]
    exact congrArg (tilt L F t h) (funext hpt)
  -- pointwise bound
  have h2 : ∀ ζ, Ft t (h + L.c t • field L.b ζ) +
      ∑ σ, ∑ τ, s * (E' σ τ - E σ τ - δ) * M ζ σ τ ≤
      -(s * (cst + δ * L.m)) + ∑ σ, ∑ τ, -(s * E σ τ) * M ζ σ τ := fun ζ => by
    set Y := h + L.c t • field L.b ζ
    have hc := hclaim Y
    have fact1 : ∑ σ, ∑ τ, s * (E' σ τ - E σ τ - δ) * M ζ σ τ =
        s * (∑ σ, ∑ τ, E' σ τ * (H t Y σ τ + m' * g t Y σ * g t Y τ)) -
          s * (m' - L.m) * (∑ σ, ∑ τ, E' σ τ * (g t Y σ * g t Y τ)) -
          s * (∑ σ, ∑ τ, E σ τ * M ζ σ τ) - s * δ * (∑ σ, ∑ τ, M ζ σ τ) := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
      simp only [hMdef, Y]; ring
    have fact2 : ∑ σ, ∑ τ, M ζ σ τ = L.m := by
      simp only [hMdef, Finset.sum_add_distrib, hF.H_sum, zero_add]
      simp only [mul_assoc, ← Finset.mul_sum, hF.g_sum, mul_one]
    have fact3 : 0 ≤ s * (m' - L.m) * (∑ σ, ∑ τ, E' σ τ * (g t Y σ * g t Y τ)) :=
      mul_nonneg (mul_nonneg hs (sub_nonneg.2 hm)) (Finset.sum_nonneg fun σ _ =>
        Finset.sum_nonneg fun τ _ => mul_nonneg (hE' σ τ)
          (mul_nonneg (hF.g_nonneg _ _ _) (hF.g_nonneg _ _ _)))
    have fact4 : ∑ σ, ∑ τ, -(s * E σ τ) * M ζ σ τ = -(s * ∑ σ, ∑ τ, E σ τ * M ζ σ τ) := by
      simp only [Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => by ring
    rw [fact1, fact2, fact4]
    linarith
  have hR : TInt L F t h fun ζ => -(s * (cst + δ * L.m)) +
      ∑ σ, ∑ τ, -(s * E σ τ) * M ζ σ τ :=
    (hF.tInt_bdd L hL t h measurable_const _ fun _ => le_rfl).add
      (TInt.sum _ fun σ _ => TInt.sum _ fun τ _ => (hM σ τ).const_mul _)
  have h3 : tilt L F t h (fun ζ => -(s * (cst + δ * L.m)) +
      ∑ σ, ∑ τ, -(s * E σ τ) * M ζ σ τ) =
      -(s * (cst + δ * L.m)) + ∑ σ, ∑ τ, -(s * E σ τ) * (levelH L F g H t h σ τ +
        L.m * levelG L F g t h σ * levelG L F g t h τ) := by
    rw [tilt_add L F t h (hF.tInt_bdd L hL t h measurable_const _ fun _ => le_rfl)
        (TInt.sum _ fun σ _ => TInt.sum _ fun τ _ => (hM σ τ).const_mul _),
      hF.tilt_const L hL t h,
      tilt_sum L F t h _ _ fun σ _ => TInt.sum _ fun τ _ => (hM σ τ).const_mul _]
    congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [tilt_sum L F t h _ _ fun τ _ => (hM σ τ).const_mul _]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [tilt_const_mul]
    congr 1
    simp only [levelH, hMdef]
    ring
  rw [h1]
  refine (hF.tilt_mono' L hL t h (TInt.add (hF.tInt_ft L hL t h) hMM) hR h2).trans
    (le_of_eq ?_)
  rw [h3]
  have : ∑ σ, ∑ τ, -(s * E σ τ) * (levelH L F g H t h σ τ +
      L.m * levelG L F g t h σ * levelG L F g t h τ) =
      -(s * ∑ σ, ∑ τ, E σ τ * (levelH L F g H t h σ τ +
        L.m * levelG L F g t h σ * levelG L F g t h τ)) := by
    simp only [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => by ring
  rw [this]; ring

end Claim

end PartB

section PartC

section LSE

variable {S : Type*} [Fintype S]

/-- Log-sum-exp. -/
private def lse (h : S → ℝ) : ℝ := Real.log (∑ σ, Real.exp (h σ))

/-- Softmax. -/
private def softmax (h : S → ℝ) (σ : S) : ℝ := Real.exp (h σ) / ∑ τ, Real.exp (h τ)

/-- Hessian of log-sum-exp. -/
private def softmaxHess [DecidableEq S] (h : S → ℝ) (σ τ : S) : ℝ :=
  (if σ = τ then softmax h σ else 0) - softmax h σ * softmax h τ

private theorem sum_exp_pos [Nonempty S] (h : S → ℝ) : 0 < ∑ σ, exp (h σ) :=
  Finset.sum_pos (fun _ _ => exp_pos _) Finset.univ_nonempty

private theorem hasFDerivAt_sum_exp (h : S → ℝ) :
    HasFDerivAt (fun h : S → ℝ => ∑ σ, exp (h σ)) (dotL fun σ => exp (h σ)) h := by
  have := HasFDerivAt.fun_sum (u := Finset.univ) fun σ _ => (hasFDerivAt_apply σ h).exp
  simpa [dotL] using this

private theorem softmax_nonneg (h : S → ℝ) (σ : S) : 0 ≤ softmax h σ :=
  div_nonneg (exp_pos _).le (Finset.sum_nonneg fun _ _ => (exp_pos _).le)

private theorem sum_softmax [Nonempty S] (h : S → ℝ) : ∑ σ, softmax h σ = 1 := by
  simp only [softmax, ← Finset.sum_div]
  exact div_self (sum_exp_pos h).ne'

private theorem softmax_le_one [Nonempty S] (h : S → ℝ) (σ : S) : softmax h σ ≤ 1 := by
  rw [← sum_softmax h]
  exact Finset.single_le_sum (f := fun τ => softmax h τ) (fun τ _ => softmax_nonneg h τ)
    (Finset.mem_univ σ)

private theorem hasFDerivAt_lse [Nonempty S] (h : S → ℝ) :
    HasFDerivAt (lse (S := S)) (dotL (softmax h)) h := by
  have := (hasFDerivAt_sum_exp h).log (sum_exp_pos h).ne'
  refine this.congr_fderiv (ContinuousLinearMap.ext fun k => ?_)
  simp only [smul_apply, dotL_apply, smul_eq_mul, softmax, Finset.mul_sum]
  exact Finset.sum_congr rfl fun σ _ => by field_simp

private theorem hasFDerivAt_softmax [Nonempty S] [DecidableEq S] (h : S → ℝ) (σ : S) :
    HasFDerivAt (fun h : S → ℝ => softmax h σ) (dotL (softmaxHess h σ)) h := by
  have hZ := hasFDerivAt_sum_exp h
  have hZinv := (hasDerivAt_inv (sum_exp_pos h).ne').comp_hasFDerivAt h hZ
  have he := (hasFDerivAt_apply σ h).exp
  have hprod := he.mul hZinv
  have hfun : (fun h : S → ℝ => softmax h σ) =
      fun h => exp (h σ) * (∑ τ, exp (h τ))⁻¹ := funext fun h => by
    simp [softmax, div_eq_mul_inv]
  rw [hfun]
  refine hprod.congr_fderiv (ContinuousLinearMap.ext fun k => ?_)
  simp only [add_apply, smul_apply, dotL_apply, smul_eq_mul, Function.comp_apply,
    softmaxHess, ContinuousLinearMap.proj_apply]
  have hZ0 := (sum_exp_pos h).ne'
  set Z := ∑ τ, exp (h τ) with hZdef
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, softmax]
  rw [← hZdef]
  have e1 : ∑ x, exp (h σ) / Z * (exp (h x) / Z) * k x =
      exp (h σ) / Z ^ 2 * ∑ x, exp (h x) * k x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by field_simp
  rw [e1]
  field_simp
  ring

/-- **Regularity of log-sum-exp.** -/
private theorem regular_lse [Nonempty S] [DecidableEq S] :
    Regular (fun (_ : ℝ) (h : S → ℝ) => lse h) (fun _ _ => 0) (fun _ h => softmax h)
      (fun _ h => softmaxHess h) 0 1 where
  hasFDerivAt t h := by
    have := (hasFDerivAt_lse h).comp (t, h)
      (hasFDerivAt_snd (𝕜 := ℝ) (p := ((t, h) : ℝ × (S → ℝ))))
    refine this.congr_fderiv (ContinuousLinearMap.ext fun p => ?_)
    simp [jointL_apply, dotL_apply]
  hess _ h σ := hasFDerivAt_softmax h σ
  ft_le _ _ := by simp
  g_nonneg _ h σ := softmax_nonneg h σ
  g_sum _ h := sum_softmax h
  H_le _ h σ τ := by
    have h1 := softmax_nonneg h σ
    have h2 := softmax_le_one h σ
    have h3 := softmax_nonneg h τ
    have h4 := softmax_le_one h τ
    unfold softmaxHess
    split_ifs with hστ
    · subst hστ
      rw [abs_le]; constructor <;> nlinarith
    · rw [zero_sub, abs_neg, abs_of_nonneg (mul_nonneg h1 h3)]
      nlinarith
  H_sum _ h := by
    unfold softmaxHess
    simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp only [← Finset.mul_sum, sum_softmax, mul_one, sub_self]

end LSE


section SK

variable {N : ℕ}

/-- The overlap sum `∑_i σ_i τ_i`. -/
private def ovl (σ τ : Fin N → Bool) : ℝ := ∑ i, spin (σ i) * spin (τ i)

/-- Guerra's comparison matrix `(β² / 2N) (∑_i σ_i τ_i - N q)²`. -/
private def Emat (β : ℝ) (N : ℕ) (q : ℝ) (σ τ : Fin N → Bool) : ℝ :=
  β ^ 2 / (2 * N) * (ovl σ τ - N * q) ^ 2

/-- `θ(x) = x ξ'(x) - ξ(x)` for the SK model. -/
private def theta (β x : ℝ) : ℝ := β ^ 2 * x ^ 2 / 2

private theorem spin_mul_self (b : Bool) : spin b * spin b = 1 := by cases b <;> simp [spin]

private theorem ovl_self (σ : Fin N → Bool) : ovl σ σ = N := by simp [ovl, spin_mul_self]

private theorem Emat_nonneg (β : ℝ) (N : ℕ) (q : ℝ) (σ τ : Fin N → Bool) : 0 ≤ Emat β N q σ τ := by
  unfold Emat; positivity

private theorem Emat_one_self (β : ℝ) (σ : Fin N → Bool) : Emat β N 1 σ σ = 0 := by
  simp [Emat, ovl_self]

/-- The Parisi level `ℓ`, with variance `ξ'(q_{ℓ+1}) - ξ'(q_ℓ) = β² (q_{ℓ+1} - q_ℓ)`. -/
private def zLevel (β : ℝ) (N : ℕ) (m q : ℕ → ℝ) (ℓ : ℕ) : Level (Fin N → Bool) where
  n := N
  m := m ℓ
  c := cos
  c' := fun t => -sin t
  b := fun i σ => Real.sqrt (β ^ 2 * (q (ℓ + 1) - q ℓ)) * spin (σ i)

/-- The vector of the coupling `g_{ij}` with `j ↦ (i₁, i₂)`. -/
private def cb (β : ℝ) (N : ℕ) (j : Fin (N * N)) (σ : Fin N → Bool) : ℝ :=
  -(β / Real.sqrt N) *
    (if (finProdFinEquiv.symm j).1 < (finProdFinEquiv.symm j).2 then
      spin (σ (finProdFinEquiv.symm j).1) * spin (σ (finProdFinEquiv.symm j).2) else 0)

/-- The level of the SK couplings. -/
private def cLevel (β : ℝ) (N : ℕ) : Level (Fin N → Bool) where
  n := N * N
  m := 0
  c := sin
  c' := cos
  b := cb β N

/-- The interpolating cascade: `casc j` is the Parisi recursion after `j` levels. -/
private def casc (β : ℝ) (N k : ℕ) (m q : ℕ → ℝ) : ℕ → ℝ → ((Fin N → Bool) → ℝ) → ℝ
  | 0 => fun _ h => lse h
  | j + 1 => levelOp (zLevel β N m q (k - j)) (casc β N k m q j)

/-- Partial sums of the correction term of the Parisi functional. -/
private def Ssum (β : ℝ) (k : ℕ) (m q : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ p ∈ Finset.Ico (k + 1 - j) (k + 1), m p * (theta β (q (p + 1)) - theta β (q p))

/-- The parameter attached to the input of a level. -/
private def mm (k : ℕ) (m : ℕ → ℝ) (j : ℕ) : ℝ := if j = 0 then 1 else m (k + 1 - j)

private theorem parisi_m_nonneg {k : ℕ} {m q : ℕ → ℝ} (hp : IsParisiParameter k m q) :
    ∀ ℓ ≤ k, 0 ≤ m ℓ := by
  intro ℓ hℓ
  induction ℓ with
  | zero => exact hp.2.1.symm.le
  | succ ℓ ih => exact (ih (by omega)).trans (hp.2.2.2.1 ℓ (by omega))

private theorem parisi_m_le_one {k : ℕ} {m q : ℕ → ℝ} (hp : IsParisiParameter k m q) :
    ∀ ℓ ≤ k, m ℓ ≤ 1 := by
  have key : ∀ d ℓ, ℓ + d = k → m ℓ ≤ 1 := by
    intro d
    induction d with
    | zero => intro ℓ h; rw [add_zero] at h; rw [h, hp.2.2.1]
    | succ d ih => intro ℓ h; exact (hp.2.2.2.1 ℓ (by omega)).trans (ih (ℓ + 1) (by omega))
  intro ℓ hℓ
  exact key (k - ℓ) ℓ (by omega)

private theorem zLevel_good (β : ℝ) (N : ℕ) {k : ℕ} {m q : ℕ → ℝ} (hp : IsParisiParameter k m q)
    {ℓ : ℕ} (hℓ : ℓ ≤ k) : (zLevel β N m q ℓ).Good where
  hc t := Real.hasDerivAt_cos t
  hcb t := abs_cos_le_one t
  hc'b t := by simp only [zLevel, abs_neg]; exact abs_sin_le_one t
  m_nonneg := parisi_m_nonneg hp ℓ hℓ
  m_le_one := parisi_m_le_one hp ℓ hℓ

private theorem cLevel_good (β : ℝ) (N : ℕ) : (cLevel β N).Good where
  hc t := Real.hasDerivAt_sin t
  hcb t := abs_sin_le_one t
  hc'b t := abs_cos_le_one t
  m_nonneg := le_rfl
  m_le_one := zero_le_one

/-- **Covariance identity of a Parisi level.** -/
private theorem zLevel_cov (β : ℝ) (hN : 0 < N) {k : ℕ} {m q : ℕ → ℝ} (hp : IsParisiParameter k m q)
    {ℓ : ℕ} (hℓ : ℓ ≤ k) (t : ℝ) (σ τ : Fin N → Bool) :
    (zLevel β N m q ℓ).c t * (zLevel β N m q ℓ).c' t *
      ∑ i, (zLevel β N m q ℓ).b i σ * (zLevel β N m q ℓ).b i τ =
    sin t * cos t * (Emat β N (q (ℓ + 1)) σ τ - Emat β N (q ℓ) σ τ -
      N * (theta β (q (ℓ + 1)) - theta β (q ℓ))) := by
  have hv : 0 ≤ β ^ 2 * (q (ℓ + 1) - q ℓ) :=
    mul_nonneg (sq_nonneg β) (sub_nonneg.2 (hp.2.2.2.2.2.2 ℓ hℓ))
  have hsum : ∑ i, (zLevel β N m q ℓ).b i σ * (zLevel β N m q ℓ).b i τ =
      β ^ 2 * (q (ℓ + 1) - q ℓ) * ovl σ τ := by
    simp only [zLevel, ovl, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := Real.mul_self_sqrt hv
    linear_combination (spin (σ i) * spin (τ i)) * this
  rw [hsum]
  simp only [zLevel, Emat, theta]
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  field_simp
  ring

/-- `∑_{i < j} a_i a_j = ((∑ a)² - ∑ a²) / 2`. -/
private theorem sum_lt_mul (a : Fin N → ℝ) :
    ∑ i, ∑ j, (if i < j then a i * a j else 0) = ((∑ i, a i) ^ 2 - ∑ i, a i ^ 2) / 2 := by
  have h1 : (∑ i, a i) ^ 2 = ∑ i, ∑ j, a i * a j := by rw [sq, Finset.sum_mul_sum]
  have h2 : ∀ i j, a i * a j = (if i < j then a i * a j else 0) +
      (if i = j then a i * a j else 0) + (if j < i then a i * a j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne, not_lt.2 h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.2 h.le]
  have h3 : ∑ i, ∑ j, (if j < i then a i * a j else 0) =
      ∑ i, ∑ j, (if i < j then a i * a j else 0) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      split_ifs <;> ring
  have h4 : ∑ i, ∑ j, (if i = j then a i * a j else 0) = ∑ i, a i ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_ite_eq]; simp [sq]
  have h5 : ∑ i, ∑ j, a i * a j = ∑ i, ∑ j, (if i < j then a i * a j else 0) +
      ∑ i, ∑ j, (if i = j then a i * a j else 0) +
      ∑ i, ∑ j, (if j < i then a i * a j else 0) := by
    simp only [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => h2 i j
  rw [h1, h5, h3, h4]; ring

/-- **Covariance identity of the coupling level.** -/
private theorem cLevel_cov (β : ℝ) (hN : 0 < N) (t : ℝ) (σ τ : Fin N → Bool) :
    (cLevel β N).c t * (cLevel β N).c' t * ∑ j, (cLevel β N).b j σ * (cLevel β N).b j τ =
    sin t * cos t * (Emat β N 0 σ τ - β ^ 2 / 2 - 0) := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hsq : Real.sqrt N ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg N)
  have hsum : ∑ j, (cLevel β N).b j σ * (cLevel β N).b j τ =
      β ^ 2 / N * ∑ i, ∑ j, (if i < j then (spin (σ i) * spin (τ i)) *
        (spin (σ j) * spin (τ j)) else 0) := by
    change ∑ j : Fin (N * N), cb β N j σ * cb β N j τ = _
    rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [cb, Equiv.symm_apply_apply]
    split_ifs
    · field_simp
      rw [hsq]; ring
    · simp
  rw [hsum, sum_lt_mul]
  have hsq1 : ∀ i, (spin (σ i) * spin (τ i)) ^ 2 = 1 := fun i => by
    rw [mul_pow, sq, sq, spin_mul_self, spin_mul_self, one_mul]
  simp only [hsq1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  simp only [cLevel, Emat, ovl]
  field_simp
  ring

end SK

section Induction

variable {N : ℕ}

private theorem sin_mul_cos_nonneg {t : ℝ} (ht : t ∈ Set.Icc 0 (π / 2)) : 0 ≤ sin t * cos t :=
  mul_nonneg (sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2, pi_pos]))
    (cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, pi_pos], ht.2⟩)

private theorem Ssum_zero (β : ℝ) (k : ℕ) (m q : ℕ → ℝ) : Ssum β k m q 0 = 0 := by
  simp [Ssum]

private theorem Ssum_succ (β : ℝ) {k : ℕ} (m q : ℕ → ℝ) {j : ℕ} (hj : j ≤ k) :
    Ssum β k m q (j + 1) = Ssum β k m q j +
      m (k - j) * (theta β (q (k - j + 1)) - theta β (q (k - j))) := by
  unfold Ssum
  rw [show k + 1 - (j + 1) = k - j by omega,
    Finset.sum_eq_sum_Ico_succ_bot (show k - j < k + 1 by omega),
    show k - j + 1 = k + 1 - j by omega]
  ring

/-- **Guerra's inequality along the Parisi levels.** -/
private theorem casc_spec (β : ℝ) (hN : 0 < N) {k : ℕ} {m q : ℕ → ℝ}
    (hp : IsParisiParameter k m q) :
    ∀ j ≤ k + 1, ∃ (Ft : ℝ → ((Fin N → Bool) → ℝ) → ℝ) (g : ℝ → ((Fin N → Bool) → ℝ) →
      (Fin N → Bool) → ℝ) (H : ℝ → ((Fin N → Bool) → ℝ) → (Fin N → Bool) → (Fin N → Bool) → ℝ)
      (K B : ℝ), Regular (casc β N k m q j) Ft g H K B ∧
      ∀ t ∈ Set.Icc 0 (π / 2), ∀ h, Ft t h ≤ -(sin t * cos t *
        (∑ σ, ∑ τ, Emat β N (q (k + 1 - j)) σ τ * (H t h σ τ + mm k m j * g t h σ * g t h τ) +
          N * Ssum β k m q j)) := by
  intro j hj
  induction j with
  | zero =>
    refine ⟨_, _, _, _, _, regular_lse, fun t _ h => ?_⟩
    have hq : q (k + 1 - 0) = 1 := by simpa using hp.2.2.2.2.2.1
    have hsum : ∑ σ, ∑ τ, Emat β N (q (k + 1 - 0)) σ τ *
        (softmaxHess h σ τ + mm k m 0 * softmax h σ * softmax h τ) = 0 := by
      rw [hq]
      refine Finset.sum_eq_zero fun σ _ => ?_
      have : ∀ τ, Emat β N 1 σ τ * (softmaxHess h σ τ + mm k m 0 * softmax h σ * softmax h τ) =
          if σ = τ then Emat β N 1 σ σ * softmax h σ else 0 := fun τ => by
        simp only [softmaxHess, mm, ite_true]
        split_ifs with hστ
        · subst hστ; ring
        · ring
      simp only [this, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Emat_one_self, zero_mul]
    rw [hsum, Ssum_zero]
    simp
  | succ j ih =>
    obtain ⟨Ft, g, H, K, B, hreg, hcl⟩ := ih (by omega)
    have hjk : j ≤ k := by omega
    have hL := zLevel_good β N hp (show k - j ≤ k by omega)
    refine ⟨_, _, _, _, _, hreg.levelOp _ hL, fun t ht h => ?_⟩
    have hs := sin_mul_cos_nonneg ht
    have hm : (zLevel β N m q (k - j)).m ≤ mm k m j := by
      simp only [zLevel, mm]
      split_ifs with hj0
      · subst hj0; exact parisi_m_le_one hp k le_rfl
      · rw [show k + 1 - j = k - j + 1 by omega]
        exact hp.2.2.2.1 (k - j) (by omega)
    have hcov : ∀ σ τ, (zLevel β N m q (k - j)).c t * (zLevel β N m q (k - j)).c' t *
        ∑ i, (zLevel β N m q (k - j)).b i σ * (zLevel β N m q (k - j)).b i τ =
        sin t * cos t * (Emat β N (q (k + 1 - j)) σ τ - Emat β N (q (k - j)) σ τ -
          N * (theta β (q (k - j + 1)) - theta β (q (k - j)))) := fun σ τ => by
      rw [zLevel_cov β hN hp (show k - j ≤ k by omega) t σ τ,
        show k - j + 1 = k + 1 - j by omega]
    have key := hreg.levelFt_le (zLevel β N m q (k - j)) hL (Emat β N (q (k - j)))
      (Emat β N (q (k + 1 - j))) (mm k m j) (N * (theta β (q (k - j + 1)) - theta β (q (k - j))))
      (N * Ssum β k m q j) (sin t * cos t) t hs hm (Emat_nonneg β N _) hcov
      (fun h => hcl t ht h) h
    have hmm : mm k m (j + 1) = m (k - j) := by
      simp only [mm, show j + 1 ≠ 0 by omega, ite_false, show k + 1 - (j + 1) = k - j by omega]
    rw [show k + 1 - (j + 1) = k - j by omega, hmm, Ssum_succ β m q hjk]
    convert key using 3
    simp only [zLevel]
    ring

/-- **Guerra's inequality at the top of the cascade.** -/
private theorem top_spec (β : ℝ) (hN : 0 < N) {k : ℕ} {m q : ℕ → ℝ} (hp : IsParisiParameter k m q) :
    ∃ (Ft : ℝ → ((Fin N → Bool) → ℝ) → ℝ) (g : ℝ → ((Fin N → Bool) → ℝ) →
      (Fin N → Bool) → ℝ) (H : ℝ → ((Fin N → Bool) → ℝ) → (Fin N → Bool) → (Fin N → Bool) → ℝ)
      (K B : ℝ), Regular (levelOp (cLevel β N) (casc β N k m q (k + 1))) Ft g H K B ∧
      ∀ t ∈ Set.Icc 0 (π / 2), ∀ h, Ft t h ≤ -(sin t * cos t * (N * Ssum β k m q (k + 1))) := by
  obtain ⟨Ft, g, H, K, B, hreg, hcl⟩ := casc_spec β hN hp (k + 1) le_rfl
  have hL := cLevel_good β N
  have hreg' := hreg.levelOp _ hL
  refine ⟨_, _, _, _, _, hreg', fun t ht h => ?_⟩
  have hs := sin_mul_cos_nonneg ht
  have hq0 : q (k + 1 - (k + 1)) = 0 := by simpa using hp.2.2.2.2.1
  have hmm : mm k m (k + 1) = 0 := by
    simp only [mm, show k + 1 ≠ 0 by omega, ite_false, Nat.sub_self]; exact hp.2.1
  have hcl' : ∀ h, Ft t h ≤ -(sin t * cos t * (∑ σ, ∑ τ, Emat β N 0 σ τ *
      (H t h σ τ + 0 * g t h σ * g t h τ) + N * Ssum β k m q (k + 1))) := fun h => by
    have := hcl t ht h
    rw [hq0, hmm] at this
    exact this
  have key := hreg.levelFt_le (cLevel β N) hL (fun _ _ => β ^ 2 / 2) (Emat β N 0) 0 0
    (N * Ssum β k m q (k + 1)) (sin t * cos t) t hs le_rfl (Emat_nonneg β N 0)
    (fun σ τ => cLevel_cov β hN t σ τ) hcl' h
  have hsum : ∑ σ, ∑ τ, (fun _ _ => β ^ 2 / 2 : (Fin N → Bool) → (Fin N → Bool) → ℝ) σ τ *
      (levelH (cLevel β N) (casc β N k m q (k + 1)) g H t h σ τ + (cLevel β N).m *
        levelG (cLevel β N) (casc β N k m q (k + 1)) g t h σ *
        levelG (cLevel β N) (casc β N k m q (k + 1)) g t h τ) = 0 := by
    have hm0 : (cLevel β N).m = 0 := rfl
    simp only [hm0, zero_mul, add_zero, ← Finset.mul_sum]
    rw [hreg'.H_sum t h, mul_zero]
  rw [hsum] at key
  simpa [cLevel] using key

end Induction

end PartC

section PartD

section Endpoints

variable {S : Type*} [Fintype S]

omit [Fintype S] in
private theorem levelOp_of_c_eq_zero (L : Level S) (F : ℝ → (S → ℝ) → ℝ) (t : ℝ) (h : S → ℝ)
    (hc : L.c t = 0) : levelOp L F t h = F t h := by
  unfold levelOp
  simp only [hc, zero_smul, add_zero, integral_const, probReal_univ, one_smul]
  split_ifs with hm
  · rfl
  · rw [Real.log_exp]; field_simp

variable {N : ℕ}

private theorem casc_pi_div_two (β : ℝ) (k : ℕ) (m q : ℕ → ℝ) (j : ℕ) (h : (Fin N → Bool) → ℝ) :
    casc β N k m q j (π / 2) h = lse h := by
  induction j generalizing h with
  | zero => rfl
  | succ j ih =>
    simp only [casc]
    rw [levelOp_of_c_eq_zero _ _ _ _ (by simp [zLevel, cos_pi_div_two]), ih]

/-- The couplings as a reindexing of a standard Gaussian vector. -/
private def couplingsOf (N : ℕ) (ζ : Fin (N * N) → ℝ) : Fin N → Fin N → ℝ :=
  fun i j => ζ (finProdFinEquiv (i, j))

private theorem couplingsOf_eq (N : ℕ) : couplingsOf N = (MeasurableEquiv.curry (Fin N) (Fin N) ℝ) ∘
    (MeasurableEquiv.piCongrLeft (fun _ => ℝ) finProdFinEquiv.symm) := by
  funext ζ i j
  simp [couplingsOf, MeasurableEquiv.coe_curry, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply, Function.curry]

private theorem measurableEmbedding_couplingsOf (N : ℕ) : MeasurableEmbedding (couplingsOf N) := by
  rw [couplingsOf_eq]
  exact (MeasurableEquiv.curry (Fin N) (Fin N) ℝ).measurableEmbedding.comp
    (MeasurableEquiv.piCongrLeft (fun _ => ℝ) finProdFinEquiv.symm).measurableEmbedding

private theorem measurePreserving_couplingsOf (N : ℕ) :
    MeasurePreserving (couplingsOf N) (stdGauss (N * N)) (couplingLaw N) := by
  have h1 := measurePreserving_piCongrLeft (fun _ : Fin N × Fin N => gaussianReal 0 1)
    finProdFinEquiv.symm
  have h2 : MeasurePreserving (MeasurableEquiv.curry (Fin N) (Fin N) ℝ)
      (Measure.pi fun _ : Fin N × Fin N => gaussianReal 0 1) (couplingLaw N) := by
    refine ⟨(MeasurableEquiv.curry _ _ _).measurable, ?_⟩
    have := Measure.infinitePi_map_curry (fun (_ : Fin N) (_ : Fin N) => gaussianReal 0 1)
    simp only [Measure.infinitePi_eq_pi] at this
    exact this
  have h3 := h2.comp h1
  rw [couplingsOf_eq]
  exact h3

private theorem field_cb (β : ℝ) (N : ℕ) (ζ : Fin (N * N) → ℝ) (σ : Fin N → Bool) :
    field (cb β N) ζ σ = hamiltonian β N (couplingsOf N ζ) σ := by
  simp only [field, cb, hamiltonian, couplingsOf]
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Equiv.symm_apply_apply]
  split_ifs <;> ring

/-- The `t = π / 2` end of Guerra's interpolation is the SK free energy. -/
private theorem top_pi_div_two (β h : ℝ) (hN : 0 < N) (k : ℕ) (m q : ℕ → ℝ) :
    levelOp (cLevel β N) (casc β N k m q (k + 1)) (π / 2)
      (fun σ => h * ∑ i, spin (σ i)) = N * freeEnergy β h N := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hm : (cLevel β N).m = 0 := rfl
  rw [levelOp, ite_eq_left hm]
  simp only [casc_pi_div_two]
  have hc : (cLevel β N).c (π / 2) = 1 := by simp [cLevel]
  simp only [hc, one_smul]
  change ∫ ζ : Fin (N * N) → ℝ, lse ((fun σ => h * ∑ i, spin (σ i)) + field (cb β N) ζ)
    ∂stdGauss (N * N) = _
  have : (fun ζ : Fin (N * N) → ℝ => lse ((fun σ => h * ∑ i, spin (σ i)) + field (cb β N) ζ)) =
      fun ζ => (fun g : Fin N → Fin N → ℝ => Real.log (∑ σ : Fin N → Bool,
        Real.exp (hamiltonian β N g σ + h * ∑ i, spin (σ i)))) (couplingsOf N ζ) := by
    funext ζ
    simp only [lse, Pi.add_apply, field_cb, add_comm]
  have key := (measurePreserving_couplingsOf N).integral_comp (measurableEmbedding_couplingsOf N)
    (fun g : Fin N → Fin N → ℝ => Real.log (∑ σ : Fin N → Bool,
      Real.exp (hamiltonian β N g σ + h * ∑ i, spin (σ i))))
  rw [this]
  refine key.trans ?_
  rw [freeEnergy]
  field_simp

end Endpoints

section ZeroEnd

/-- One-Lipschitz real functions. -/
private def OneLip (f : ℝ → ℝ) : Prop := ∀ x y, |f x - f y| ≤ |x - y|

private theorem OneLip.continuous {f : ℝ → ℝ} (hf : OneLip f) : Continuous f :=
  (LipschitzWith.of_dist_le_mul (K := 1) fun x y => by
    simpa [Real.dist_eq] using hf x y).continuous

private theorem OneLip.abs_shift_le {f : ℝ → ℝ} (hf : OneLip f) (y z : ℝ) :
    |f (y + z)| ≤ |f 0| + |y| + |z| := by
  have := hf (y + z) 0
  have h2 := _root_.abs_add_le y z
  have h3 := abs_sub_abs_le_abs_sub (f (y + z)) (f 0)
  simp only [sub_zero] at this
  linarith

private theorem oneLip_log_cosh : OneLip fun y => Real.log (Real.cosh y) := by
  have key : ∀ x y, Real.log (cosh x) ≤ Real.log (cosh y) + |x - y| := fun x y => by
    have hcx := cosh_pos x
    have hcy := cosh_pos y
    rw [← Real.log_exp |x - y|, ← Real.log_mul hcy.ne' (exp_pos _).ne']
    refine Real.log_le_log hcx ?_
    rw [cosh_eq, cosh_eq]
    have h1 : exp x ≤ exp y * exp |x - y| := by
      rw [← exp_add]; exact exp_le_exp.2 (by linarith [le_abs_self (x - y)])
    have h2 : exp (-x) ≤ exp (-y) * exp |x - y| := by
      rw [← exp_add]; exact exp_le_exp.2 (by linarith [neg_abs_le (x - y)])
    nlinarith
  intro x y
  rw [abs_le]
  constructor
  · have := key y x; rw [abs_sub_comm] at this; linarith
  · linarith [key x y]

private theorem integrable_exp_mul_abs_gaussian (v : NNReal) (a : ℝ) :
    Integrable (fun x : ℝ => exp (a * |x|)) (gaussianReal 0 v) := by
  refine ((integrable_exp_mul_gaussianReal (μ := 0) (v := v) |a|).add
    (integrable_exp_mul_gaussianReal (μ := 0) (v := v) (-|a|))).mono'
    (by fun_prop) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), Pi.add_apply]
  have h1 : a * |x| ≤ |a| * |x| := mul_le_mul_of_nonneg_right (le_abs_self a) (abs_nonneg x)
  have e1 := exp_pos (|a| * x)
  have e2 := exp_pos (-|a| * x)
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx] at h1 ⊢
    have := exp_le_exp.mpr h1
    linarith
  · rw [abs_of_nonpos hx] at h1 ⊢
    have := exp_le_exp.mpr (show a * -x ≤ -|a| * x by linarith)
    linarith

private theorem OneLip.integrable {f : ℝ → ℝ} (hf : OneLip f) (v : NNReal) (y : ℝ) :
    Integrable (fun z => f (y + z)) (gaussianReal 0 v) := by
  refine ((integrable_exp_mul_abs_gaussian v 1).const_mul (|f 0| + |y| + 1)).mono'
    (hf.continuous.comp (continuous_const.add continuous_id)).aestronglyMeasurable
    (ae_of_all _ fun z => ?_)
  rw [Real.norm_eq_abs]
  have h1 := hf.abs_shift_le y z
  have h2 : |z| ≤ exp (1 * |z|) := by
    have := add_one_le_exp |z|; rw [one_mul]; linarith
  have h3 : 1 ≤ exp (1 * |z|) := one_le_exp (by positivity)
  nlinarith [abs_nonneg (f 0), abs_nonneg y]

private theorem OneLip.integrable_exp {f : ℝ → ℝ} (hf : OneLip f) (v : NNReal) {m : ℝ} (hm0 : 0 ≤ m)
    (hm1 : m ≤ 1) (y : ℝ) :
    Integrable (fun z => exp (m * f (y + z))) (gaussianReal 0 v) := by
  refine ((integrable_exp_mul_abs_gaussian v 1).const_mul (exp (|f 0| + |y|))).mono'
    ((continuous_const.mul (hf.continuous.comp (continuous_const.add continuous_id))).rexp
      ).aestronglyMeasurable (ae_of_all _ fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), ← exp_add]
  refine (exp_mul_le_exp_abs hm0 hm1 _).trans (exp_le_exp.2 ?_)
  have := hf.abs_shift_le y z
  linarith

private theorem OneLip.step {f : ℝ → ℝ} (hf : OneLip f) (v : ℝ) {m : ℝ} (hm0 : 0 ≤ m)
    (hm1 : m ≤ 1) : OneLip (parisiStep v m f) := by
  intro x y
  unfold parisiStep
  split_ifs with hm
  · rw [← integral_sub (hf.integrable _ x) (hf.integrable _ y)]
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ z, |f (x + z) - f (y + z)| ∂gaussianReal 0 v.toNNReal
        ≤ ∫ _z, |x - y| ∂gaussianReal 0 v.toNNReal :=
          integral_mono ((hf.integrable _ x).sub (hf.integrable _ y)).abs
            (integrable_const _) fun z => by
              have := hf (x + z) (y + z)
              simpa using this
      _ = |x - y| := by simp
  · have hmpos : 0 < m := lt_of_le_of_ne hm0 (Ne.symm hm)
    have key : ∀ x y, 1 / m * Real.log (∫ z, exp (m * f (x + z)) ∂gaussianReal 0 v.toNNReal) ≤
        1 / m * Real.log (∫ z, exp (m * f (y + z)) ∂gaussianReal 0 v.toNNReal) + |x - y| := by
      intro x y
      have hIx := integral_exp_pos (hf.integrable_exp v.toNNReal hm0 hm1 x)
      have hIy := integral_exp_pos (hf.integrable_exp v.toNNReal hm0 hm1 y)
      have hle : ∫ z, exp (m * f (x + z)) ∂gaussianReal 0 v.toNNReal ≤
          exp (m * |x - y|) * ∫ z, exp (m * f (y + z)) ∂gaussianReal 0 v.toNNReal := by
        rw [← integral_const_mul]
        refine integral_mono (hf.integrable_exp v.toNNReal hm0 hm1 x)
          ((hf.integrable_exp v.toNNReal hm0 hm1 y).const_mul _) fun z => ?_
        simp only
        rw [← exp_add]
        refine exp_le_exp.2 ?_
        have := hf (x + z) (y + z)
        have h' : f (x + z) ≤ f (y + z) + |x - y| := by
          have : |(x + z) - (y + z)| = |x - y| := by ring_nf
          linarith [le_abs_self (f (x + z) - f (y + z))]
        nlinarith
      have hlog := Real.log_le_log hIx hle
      rw [Real.log_mul (exp_pos _).ne' hIy.ne', Real.log_exp] at hlog
      have : 1 / m * Real.log (∫ z, exp (m * f (x + z)) ∂gaussianReal 0 v.toNNReal) ≤
          1 / m * (m * |x - y| + Real.log (∫ z, exp (m * f (y + z)) ∂gaussianReal 0 v.toNNReal)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      rw [mul_add, ← mul_assoc, one_div_mul_cancel hmpos.ne', one_mul] at this
      linarith
    rw [abs_le]
    constructor
    · have := key y x; rw [abs_sub_comm] at this; linarith
    · linarith [key x y]

variable {N : ℕ}

private theorem oneLip_parisiRecursion (β : ℝ) {k : ℕ} {m q : ℕ → ℝ}
    (hp : IsParisiParameter k m q) :
    ∀ j ≤ k + 1, OneLip (parisiRecursion (deriv (skCovariance β)) k m q j) := by
  intro j hj
  induction j with
  | zero => exact oneLip_log_cosh
  | succ j ih =>
    exact (ih (by omega)).step _ (parisi_m_nonneg hp _ (by omega))
      (parisi_m_le_one hp _ (by omega))

private theorem deriv_skCovariance (β : ℝ) : deriv (skCovariance β) = fun x => β ^ 2 * x := by
  funext x
  have : HasDerivAt (skCovariance β) (β ^ 2 * x) x := by
    have := ((hasDerivAt_pow 2 x).const_mul (β ^ 2)).div_const 2
    convert this using 1
    · funext y; simp [skCovariance]
    · push_cast; ring
  exact this.deriv

private theorem lse_product (y : Fin N → ℝ) :
    lse (fun σ : Fin N → Bool => ∑ i, y i * spin (σ i)) =
      N * Real.log 2 + ∑ i, Real.log (Real.cosh (y i)) := by
  unfold lse
  have : ∑ σ : Fin N → Bool, exp (∑ i, y i * spin (σ i)) = ∏ i, (2 * Real.cosh (y i)) := by
    simp_rw [Real.exp_sum]
    rw [← Fintype.prod_sum (fun i (b : Bool) => exp (y i * spin b))]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [spin, Real.cosh_eq]
    ring
  rw [this, Real.log_prod (fun i _ => by positivity)]
  simp only [Real.log_mul (two_ne_zero) (cosh_pos _).ne', Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

private theorem integral_sqrt_mul_gaussian (φ : ℝ → ℝ) (hφ : Continuous φ) {v : ℝ} (hv : 0 ≤ v) :
    ∫ x, φ (Real.sqrt v * x) ∂gaussianReal 0 1 = ∫ z, φ z ∂gaussianReal 0 v.toNNReal := by
  have hmap := gaussianReal_map_const_mul (μ := 0) (v := 1) (Real.sqrt v)
  have hv' : gaussianReal (Real.sqrt v * 0) (.mk (Real.sqrt v ^ 2) (sq_nonneg _) * 1) =
      gaussianReal 0 v.toNNReal := by
    congr 1
    · ring
    · ext; simp [Real.sq_sqrt hv, max_eq_left hv]
  rw [← hv', ← hmap, integral_map (by fun_prop) hφ.aestronglyMeasurable]

end ZeroEnd

section Factor

variable {N : ℕ}

private theorem OneLip.integrable_scaled {f : ℝ → ℝ} (hf : OneLip f) (y c : ℝ) :
    Integrable (fun x => f (y + c * x)) (gaussianReal 0 1) := by
  refine ((integrable_exp_mul_abs_gaussian 1 1).const_mul (|f 0| + |y| + |c|)).mono'
    (hf.continuous.comp (continuous_const.add (continuous_const.mul continuous_id))
      ).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs]
  have h1 := hf.abs_shift_le y (c * x)
  rw [abs_mul] at h1
  have h2 : |x| ≤ exp (1 * |x|) := by
    have := add_one_le_exp |x|; rw [one_mul]; linarith
  have h3 : 1 ≤ exp (1 * |x|) := one_le_exp (by positivity)
  nlinarith [abs_nonneg (f 0), abs_nonneg y, abs_nonneg c, abs_nonneg x]

private theorem OneLip.integrable_exp_scaled {f : ℝ → ℝ} (hf : OneLip f) {m : ℝ} (hm0 : 0 ≤ m)
    (hm1 : m ≤ 1) (y c : ℝ) :
    Integrable (fun x => exp (m * f (y + c * x))) (gaussianReal 0 1) := by
  refine ((integrable_exp_mul_abs_gaussian 1 |c|).const_mul (exp (|f 0| + |y|))).mono'
    ((continuous_const.mul (hf.continuous.comp (continuous_const.add
      (continuous_const.mul continuous_id)))).rexp).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), ← exp_add]
  refine (exp_mul_le_exp_abs hm0 hm1 _).trans (exp_le_exp.2 ?_)
  have := hf.abs_shift_le y (c * x)
  rw [abs_mul] at this
  linarith

/-- **Site factorization at `t = 0`**: without couplings the cascade is a sum over the sites of
the one-variable Parisi recursion. -/
private theorem casc_zero (β : ℝ) {k : ℕ} {m q : ℕ → ℝ} (hp : IsParisiParameter k m q) :
    ∀ j ≤ k + 1, ∀ y : Fin N → ℝ, casc β N k m q j 0 (fun σ => ∑ i, y i * spin (σ i)) =
      N * Real.log 2 + ∑ i, parisiRecursion (deriv (skCovariance β)) k m q j (y i) := by
  intro j hj
  induction j with
  | zero => intro y; exact lse_product y
  | succ j ih =>
    intro y
    have hjk : j ≤ k := by omega
    set f := parisiRecursion (deriv (skCovariance β)) k m q j with hf
    have hfL : OneLip f := oneLip_parisiRecursion β hp j (by omega)
    set v := β ^ 2 * (q (k - j + 1) - q (k - j)) with hv
    have hv0 : 0 ≤ v := mul_nonneg (sq_nonneg β) (sub_nonneg.2 (hp.2.2.2.2.2.2 _ (by omega)))
    have hm0 := parisi_m_nonneg hp (k - j) (by omega)
    have hm1 := parisi_m_le_one hp (k - j) (by omega)
    have hshift : ∀ ζ : Fin N → ℝ, (fun σ => ∑ i, y i * spin (σ i)) +
        (zLevel β N m q (k - j)).c 0 • field (zLevel β N m q (k - j)).b ζ =
        fun σ => ∑ i, (y i + Real.sqrt v * ζ i) * spin (σ i) := by
      intro ζ
      funext σ
      simp only [zLevel, field, Pi.add_apply, cos_zero, one_smul, add_mul,
        Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    have hrec : parisiRecursion (deriv (skCovariance β)) k m q (j + 1) =
        parisiStep v (m (k - j)) f := by
      simp only [parisiRecursion, deriv_skCovariance, hf]
      congr 1
      rw [hv]; ring
    have hint : ∀ ζ : Fin N → ℝ, casc β N k m q j 0
        ((fun σ => ∑ i, y i * spin (σ i)) +
          (zLevel β N m q (k - j)).c 0 • field (zLevel β N m q (k - j)).b ζ) =
        N * Real.log 2 + ∑ i, f (y i + Real.sqrt v * ζ i) := fun ζ => by
      rw [hshift ζ, ih (by omega)]
    have h1d : ∀ (φ : ℝ → ℝ), Continuous φ → ∀ i : Fin N,
        ∫ ζ : Fin N → ℝ, φ (y i + Real.sqrt v * ζ i) ∂stdGauss N =
        ∫ z, φ (y i + z) ∂gaussianReal 0 v.toNNReal := fun φ hφ i => by
      have := integral_comp_eval (μ := fun _ : Fin N => gaussianReal 0 1) (i := i)
        (f := fun x => φ (y i + Real.sqrt v * x))
        (hφ.comp (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable
      exact this.trans (integral_sqrt_mul_gaussian (fun z => φ (y i + z))
        (hφ.comp (continuous_const.add continuous_id)) hv0)
    change levelOp (zLevel β N m q (k - j)) (casc β N k m q j) 0 _ = _
    rw [hrec]
    unfold levelOp parisiStep
    have hmz : (zLevel β N m q (k - j)).m = m (k - j) := rfl
    simp only [hmz]
    split_ifs with hm
    · -- the level is a plain expectation
      change ∫ ζ : Fin N → ℝ, casc β N k m q j 0 ((fun σ => ∑ i, y i * spin (σ i)) +
        (zLevel β N m q (k - j)).c 0 • field (zLevel β N m q (k - j)).b ζ) ∂stdGauss N = _
      simp only [hint]
      have hi : ∀ i : Fin N, Integrable (fun ζ : Fin N → ℝ => f (y i + Real.sqrt v * ζ i))
          (stdGauss N) := fun i => by
        unfold stdGauss
        exact integrable_comp_eval (μ := fun _ : Fin N => gaussianReal 0 1) (i := i)
          (hfL.integrable_scaled (y i) (Real.sqrt v))
      rw [integral_add (integrable_const _) (integrable_finsetSum _ fun i _ => hi i),
        integral_const, probReal_univ, one_smul, integral_finsetSum _ fun i _ => hi i]
      congr 1
      exact Finset.sum_congr rfl fun i _ => h1d f hfL.continuous i
    · -- the level is a tilted expectation
      change 1 / m (k - j) * Real.log (∫ ζ : Fin N → ℝ, exp (m (k - j) *
        casc β N k m q j 0 ((fun σ => ∑ i, y i * spin (σ i)) +
          (zLevel β N m q (k - j)).c 0 • field (zLevel β N m q (k - j)).b ζ)) ∂stdGauss N) = _
      simp only [hint]
      have hprod : ∀ ζ : Fin N → ℝ, exp (m (k - j) * (N * Real.log 2 +
          ∑ i, f (y i + Real.sqrt v * ζ i))) = exp (m (k - j) * (N * Real.log 2)) *
          ∏ i, exp (m (k - j) * f (y i + Real.sqrt v * ζ i)) := fun ζ => by
        rw [mul_add, exp_add, Finset.mul_sum, Real.exp_sum]
      simp only [hprod]
      rw [integral_const_mul]
      have hfac : ∫ ζ : Fin N → ℝ, ∏ i, exp (m (k - j) * f (y i + Real.sqrt v * ζ i))
          ∂stdGauss N = ∏ i, ∫ z, exp (m (k - j) * f (y i + z)) ∂gaussianReal 0 v.toNNReal := by
        unfold stdGauss
        rw [integral_fintype_prod_eq_prod (f := fun i x => exp (m (k - j) * f (y i +
          Real.sqrt v * x)))]
        refine Finset.prod_congr rfl fun i _ => ?_
        exact integral_sqrt_mul_gaussian (fun z => exp (m (k - j) * f (y i + z)))
          ((continuous_const.mul (hfL.continuous.comp
            (continuous_const.add continuous_id))).rexp) hv0
      rw [hfac]
      have hpos : ∀ i : Fin N, 0 < ∫ z, exp (m (k - j) * f (y i + z)) ∂gaussianReal 0 v.toNNReal :=
        fun i => integral_exp_pos (hfL.integrable_exp v.toNNReal hm0 hm1 (y i))
      rw [Real.log_mul (exp_pos _).ne' (Finset.prod_pos fun i _ => hpos i).ne', Real.log_exp,
        Real.log_prod fun i _ => (hpos i).ne', mul_add, Finset.mul_sum]
      congr 1
      field_simp

private theorem top_zero (β h : ℝ) {k : ℕ} {m q : ℕ → ℝ} (hp : IsParisiParameter k m q) :
    levelOp (cLevel β N) (casc β N k m q (k + 1)) 0 (fun σ => h * ∑ i, spin (σ i)) =
      N * (Real.log 2 + parisiRecursion (deriv (skCovariance β)) k m q (k + 1) h) := by
  rw [levelOp_of_c_eq_zero _ _ _ _ (by simp [cLevel])]
  have : (fun σ : Fin N → Bool => h * ∑ i, spin (σ i)) =
      fun σ => ∑ i, (fun _ => h) i * spin (σ i) := by
    funext σ; simp [Finset.mul_sum]
  rw [this, casc_zero β hp (k + 1) le_rfl]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end Factor

section Main

variable {N : ℕ}

private theorem parisiFunctional_sk (β h : ℝ) {k : ℕ} {m q : ℕ → ℝ} (hp : IsParisiParameter k m q) :
    parisiFunctional (skCovariance β) h k m q =
      Real.log 2 + parisiRecursion (deriv (skCovariance β)) k m q (k + 1) h -
        Ssum β k m q (k + 1) / 2 := by
  unfold parisiFunctional
  simp only [deriv_skCovariance]
  congr 1
  have hS : Ssum β k m q (k + 1) = ∑ ℓ ∈ Finset.Icc 1 k, m ℓ *
      ((q (ℓ + 1) * (β ^ 2 * q (ℓ + 1)) - skCovariance β (q (ℓ + 1))) -
        (q ℓ * (β ^ 2 * q ℓ) - skCovariance β (q ℓ))) := by
    unfold Ssum
    rw [Nat.sub_self, Finset.sum_eq_sum_Ico_succ_bot (show 0 < k + 1 by omega), hp.2.1, zero_mul,
      zero_add, ← Finset.Ico_add_one_right_eq_Icc]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    simp only [theta, skCovariance]
    ring
  rw [hS]
  ring

end Main

end PartD

end

end MathlibExt.Probability.ParisiFormulaWanted.Guerra

namespace MathlibExt.Probability.ParisiFormulaWanted

open Filter Topology Real MathlibExt.Probability.SherringtonKirkpatrick

/-- **Guerra's replica-symmetry-breaking bound for the SK model at every system size.**
For every `β`, every field `h`, all admissible Parisi parameters `k, m, q` and every `N ≥ 1`, the
free energy of the SK model satisfies `F_N ≤ P_k(m, q)`, where `P_k` is the Parisi functional for
`ξ(x) = β² x² / 2`.

Source: F. Guerra, *Broken replica symmetry bounds in the mean field spin glass model*, Comm.
Math. Phys. 233 (2003), 1–12; arXiv:cond-mat/0205123, Section 4, Theorem 3 (its first bound, for
a piecewise constant functional order parameter; the source writes the field term as
`βh ∑_i σ_i`). -/
theorem freeEnergy_le_parisiFunctional (β h : ℝ) {N : ℕ} (hN : 0 < N) {k : ℕ} {m q : ℕ → ℝ}
    (hp : IsParisiParameter k m q) :
    freeEnergy β h N ≤ parisiFunctional (skCovariance β) h k m q := by
  obtain ⟨Ft, g, H, K, B, hreg, hcl⟩ := Guerra.top_spec β hN hp
  set h₀ : (Fin N → Bool) → ℝ := fun σ => h * ∑ i, spin (σ i) with hh₀
  set S := Guerra.Ssum β k m q (k + 1) with hS
  set Γ : ℝ → ℝ := fun t =>
    Guerra.levelOp (Guerra.cLevel β N) (Guerra.casc β N k m q (k + 1)) t h₀ +
      N * S / 2 * sin t ^ 2 with hΓ
  have hderiv : ∀ t, HasDerivAt Γ (Ft t h₀ + N * S * (sin t * cos t)) t := fun t => by
    have h1 := hreg.hasDerivAt_t t h₀
    have h2 : HasDerivAt (fun t => N * S / 2 * sin t ^ 2) (N * S * (sin t * cos t)) t := by
      have := ((Real.hasDerivAt_sin t).pow 2).const_mul (N * S / 2)
      convert this using 1
      push_cast; ring
    exact h1.add h2
  have hanti : AntitoneOn Γ (Set.Icc 0 (π / 2)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) ?_ ?_ ?_
    · exact (continuous_iff_continuousAt.2 fun t => (hderiv t).continuousAt).continuousOn
    · exact fun t _ => (hderiv t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hderiv t).deriv]
      have := hcl t (Set.Ioo_subset_Icc_self ht) h₀
      nlinarith
  have hpi : (0 : ℝ) ≤ π / 2 := by positivity
  have hle := hanti (Set.left_mem_Icc.2 hpi) (Set.right_mem_Icc.2 hpi) hpi
  simp only [hΓ, hh₀, Guerra.top_pi_div_two β h hN, Guerra.top_zero β h hp, sin_pi_div_two,
    sin_zero] at hle
  rw [Guerra.parisiFunctional_sk β h hp, ← hS]
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have : (N : ℝ) * freeEnergy β h N ≤
      N * (Real.log 2 + parisiRecursion (deriv (skCovariance β)) k m q (k + 1) h - S / 2) := by
    nlinarith
  exact le_of_mul_le_mul_left this hN'

-- The hypothesis `hβ` is kept to match the stated theorem; the bound holds for every `β`
-- (`freeEnergy_le_parisiFunctional`).
set_option linter.unusedVariables false in
/-- **Guerra's replica-symmetry-breaking bound for the SK model** (Talagrand, *The Parisi
formula*, Ann. of Math. 163 (2006), discussion after Theorem 1.1: Guerra proves that the left-hand
side of (1.14) is bounded by its right-hand side). For `β > 0`, every field `h` and all admissible
Parisi parameters `k, m, q`, `limsup_N F_N ≤ P_k(m, q)`. -/
theorem freeEnergy_le_parisiFunctional_eventually (β h : ℝ) (hβ : 0 < β) {k : ℕ}
    {m q : ℕ → ℝ} (hp : IsParisiParameter k m q) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, freeEnergy β h N ≤ parisiFunctional (skCovariance β) h k m q + ε := by
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (freeEnergy_le_parisiFunctional β h hN hp).trans (le_add_of_nonneg_right hε.le)

end MathlibExt.Probability.ParisiFormulaWanted

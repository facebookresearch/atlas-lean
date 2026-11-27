/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# Positive Fourier decay of a circle measure extends to L^1 densities

The following OpenBMB notice applies to the adapted statement and its documentation.

Copyright (c) 2026 OpenBMB

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

Attribution and modification notice: the statement below is taken from openbmb/ma-proofbench at
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_13.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782), distributed under the MIT License above.
See also the Hugging Face dataset openbmb/MA-ProofBench. Changes made: converted
`theorem ma_proofbench_l2_13 … := by sorry` into the Batteries `theorem_wanted`
`tendsto_integral_pow_mul_of_tendsto_integral_pow`; moved the informal problem statement
docstring onto it and placed the declarations in namespace
`MathlibExt.MeasureTheory.CircleMeasureFourierDecayIntegrableWanted`; replaced `import Mathlib`
by `public import Mathlib` under the module system.
This move supplies a proof and narrows the imports to the modules used.
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Group.Circle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Fourier decay of circle measures under integrable weighting

Transport the measure to the additive circle. Shifting a moment gives decay against every
Fourier monomial. Use uniform density for continuous functions, then the integral norm to
approximate an arbitrary integrable weight. The measure need not be Haar measure.
-/

@[expose] public section

namespace MathlibExt.MeasureTheory.CircleMeasureFourierDecayIntegrableWanted

open _root_.MeasureTheory Filter Set
open scoped ENNReal Topology

noncomputable section

private abbrev A := AddCircle (1 : ℝ)
private instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

private def e : A ≃ₜ Circle := AddCircle.homeomorphCircle one_ne_zero
private def z (x : A) : ℂ := (e x : ℂ)

private theorem z_cont : Continuous z := continuous_subtype_val.comp e.continuous
private theorem z_norm (x : A) : ‖z x‖ = 1 := Circle.norm_coe (e x)
private theorem z_ne (x : A) : z x ≠ 0 := Circle.coe_ne_zero (e x)

private theorem fourier_eq_zpow (j : ℤ) (x : A) : fourier j x = z x ^ j := by
  rw [fourier_apply, AddCircle.toCircle_zsmul, Circle.coe_zpow, z, e,
    AddCircle.homeomorphCircle_apply]

private def moment (ν : Measure A) (n : ℕ) (g : A → ℂ) : ℂ :=
  ∫ x, z x ^ n * g x ∂ν

private theorem weighted_int {ν : Measure A} (n : ℕ) {g : A → ℂ} (hg : Integrable g ν) :
    Integrable (fun x => z x ^ n * g x) ν := by
  apply hg.bdd_mul (c := 1) (z_cont.pow n).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    change ‖z x ^ n‖ ≤ 1
    rw [norm_pow, z_norm, one_pow]

private theorem moment_sub {ν : Measure A} (n : ℕ) {f g : A → ℂ}
    (hf : Integrable f ν) (hg : Integrable g ν) :
    moment ν n f - moment ν n g = moment ν n (fun x => f x - g x) := by
  simp only [moment, mul_sub]
  exact (integral_sub (weighted_int n hf) (weighted_int n hg)).symm

private theorem norm_moment_le {ν : Measure A} (n : ℕ) (g : A → ℂ) :
    ‖moment ν n g‖ ≤ ∫ x, ‖g x‖ ∂ν := by
  unfold moment
  calc
    _ ≤ ∫ x, ‖z x ^ n * g x‖ ∂ν := norm_integral_le_integral_norm _
    _ = _ := by simp only [norm_mul, norm_pow, z_norm, one_pow, one_mul]

private theorem continuous_integrable {ν : Measure A} [IsFiniteMeasure ν] (g : C(A, ℂ)) :
    Integrable g ν :=
  Integrable.of_bound g.continuous.aestronglyMeasurable ‖g‖
    (Eventually.of_forall g.norm_coe_le_norm)

private theorem tendsto_basic {ν : Measure A}
    (h : Tendsto (fun n : ℕ => ∫ x, z x ^ n ∂ν) atTop (𝓝 0)) (j : ℤ) :
    Tendsto (fun n : ℕ => moment ν n (fourier j)) atTop (𝓝 0) := by
  let k (n : ℕ) := ((n : ℤ) + j).toNat
  have hk : Tendsto k atTop atTop := by
    refine tendsto_atTop.2 fun m => ?_
    filter_upwards [eventually_ge_atTop (m + j.natAbs)] with n hn
    dsimp [k]
    omega
  apply (h.comp hk).congr'
  filter_upwards [eventually_ge_atTop j.natAbs] with n hn
  have hj : 0 ≤ (n : ℤ) + j := by omega
  change (∫ x, z x ^ k n ∂ν) = moment ν n (fourier j)
  unfold moment
  congr 1
  funext x
  rw [fourier_eq_zpow, ← zpow_natCast, ← zpow_natCast (z x) n, ← zpow_add₀ (z_ne x)]
  simp only [k, Int.toNat_of_nonneg hj]

private theorem tendsto_span {ν : Measure A} [IsFiniteMeasure ν]
    (h : Tendsto (fun n : ℕ => ∫ x, z x ^ n ∂ν) atTop (𝓝 0))
    {g : C(A, ℂ)} (hg : g ∈ Submodule.span ℂ (range (fourier (T := 1)))) :
    Tendsto (fun n : ℕ => moment ν n g) atTop (𝓝 0) := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨j, rfl⟩ := hg
    exact tendsto_basic h j
  | zero => simp [moment]
  | add g q _ _ hg hq =>
    have heq (n : ℕ) : moment ν n (g + q : C(A, ℂ)) = moment ν n g + moment ν n q := by
      simp only [moment, ContinuousMap.add_apply, mul_add]
      exact integral_add (weighted_int n (continuous_integrable g))
        (weighted_int n (continuous_integrable q))
    simpa only [heq, add_zero] using hg.add hq
  | smul c g _ hg =>
    have heq (n : ℕ) : moment ν n (c • g : C(A, ℂ)) = c * moment ν n g := by
      unfold moment
      simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_left_comm (z _ ^ n) c]
      exact integral_const_mul _ _
    simpa only [heq, mul_zero] using tendsto_const_nhds.mul hg

private theorem tendsto_weighted {ν : Measure A} [IsFiniteMeasure ν]
    (h : Tendsto (fun n : ℕ => ∫ x, z x ^ n ∂ν) atTop (𝓝 0))
    {f : A → ℂ} (hf : Integrable f ν) :
    Tendsto (fun n : ℕ => moment ν n f) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨g, hg, hgi⟩ := hf.exists_boundedContinuous_integral_sub_le (show 0 < ε / 3 by positivity)
  let G : C(A, ℂ) := g.toContinuousMap
  let δ : ℝ := (ε / 3) / (ν.real univ + 1)
  have hm : 0 ≤ ν.real univ := ENNReal.toReal_nonneg
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hG : G ∈ closure (↑(Submodule.span ℂ (range (fourier (T := 1)))) : Set C(A, ℂ)) := by
    rw [← Submodule.topologicalClosure_coe, span_fourier_closure_eq_top]
    exact Submodule.mem_top
  obtain ⟨q, hq, hGq⟩ := Metric.mem_closure_iff.mp hG δ hδ
  have hq_lim := Metric.tendsto_nhds.mp (tendsto_span h hq) (ε / 3) (by positivity)
  have hδμ : δ * ν.real univ ≤ ε / 3 := calc
    _ ≤ δ * (ν.real univ + 1) := mul_le_mul_of_nonneg_left (by linarith) hδ.le
    _ = ε / 3 := div_mul_cancel₀ _ (by positivity)
  filter_upwards [hq_lim] with n hn
  rw [dist_zero_right] at hn ⊢
  have hfg : ‖moment ν n f - moment ν n g‖ ≤ ε / 3 := by
    rw [moment_sub n hf hgi]
    exact (norm_moment_le n _).trans hg
  have hgq : ‖moment ν n g - moment ν n q‖ ≤ ε / 3 := by
    rw [moment_sub n hgi (continuous_integrable q)]
    apply le_trans (norm_integral_le_of_norm_le_const ?_) hδμ
    exact Eventually.of_forall fun x => calc
      ‖z x ^ n * (g x - q x)‖ = ‖g x - q x‖ := by rw [norm_mul, norm_pow, z_norm, one_pow, one_mul]
      _ ≤ ‖G - q‖ := (G - q).norm_coe_le_norm x
      _ ≤ δ := (dist_eq_norm G q ▸ hGq).le
  calc
    ‖moment ν n f‖ = ‖(moment ν n f - moment ν n g) +
        ((moment ν n g - moment ν n q) + moment ν n q)‖ := by congr 1; ring
    _ ≤ ‖moment ν n f - moment ν n g‖ +
        (‖moment ν n g - moment ν n q‖ + ‖moment ν n q‖) := by
      exact (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
    _ < ε := by linarith
/-- **Fourier decay of a circle measure passes to integrable densities.** Let $\mu$ be a finite
Borel measure on $\mathbb{C}$ concentrated on the unit circle $T = \{z \in \mathbb{C} : |z| = 1\}$,
that is, $\mu$-almost every $z$ lies in $T$, and suppose that $\int z^n \, d\mu(z) \to 0$ as
$n \to \infty$ through $\mathbb{N}$. Then for every $\mu$-integrable function
$f : \mathbb{C} \to \mathbb{C}$,
$$
\lim_{n \to \infty} \int z^n f(z) \, d\mu(z) = 0.
$$

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Measure and integration; Set
functions and measures on spaces with additional structure),
`benchmark/level2/ma_proofbench_l2_13.lean` at openbmb/ma-proofbench@31bab4c.
-/
theorem tendsto_integral_pow_mul_of_tendsto_integral_pow
    (μ : MeasureTheory.Measure ℂ)
    (hfinite : μ Set.univ < ⊤)
    (hsphere : ∀ᵐ z ∂μ, z ∈ Metric.sphere (0 : ℂ) 1)
    (hpow : Filter.Tendsto (fun n : ℕ => ∫ z, z ^ n ∂μ) Filter.atTop (nhds 0))
    (f : ℂ → ℂ)
    (hf : MeasureTheory.Integrable f μ) :
    Filter.Tendsto (fun n : ℕ => ∫ z, z ^ n * f z ∂μ) Filter.atTop (nhds 0) := by
  have hme : MeasurableEmbedding z :=
    (MeasurableEmbedding.subtype_coe Metric.isClosed_sphere.measurableSet).comp
      e.measurableEmbedding
  have hr : range z = Metric.sphere (0 : ℂ) 1 := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (e x).property
    · intro hy
      let c : Circle := (⟨y, hy⟩ : ↥(Metric.sphere (0 : ℂ) 1))
      exact ⟨e.symm c, congrArg (fun u : Circle => (u : ℂ)) (e.apply_symm_apply c)⟩
  let ν : Measure A := μ.comap z
  have hmap : ν.map z = μ := by
    rw [hme.map_comap, hr, Measure.restrict_eq_self_of_ae_mem hsphere]
  have hν : ν univ = μ univ := by
    rw [← hmap, Measure.map_apply hme.measurable MeasurableSet.univ, preimage_univ]
  let : IsFiniteMeasure ν := ⟨by rwa [hν]⟩
  rw [← hmap] at hpow hf ⊢
  simp only [hme.integral_map] at hpow ⊢
  exact tendsto_weighted hpow (hme.integrable_map_iff.mp hf)

end

end MathlibExt.MeasureTheory.CircleMeasureFourierDecayIntegrableWanted

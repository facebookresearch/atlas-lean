/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.GilPelaez
public import MathlibExt.Analysis.WeightedChiSquare
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Davies' p-value formula for a weighted chi-square mixture

For `Q ~ ∑ⱼ λⱼ χ²₁` (`MathlibExt.Analysis.WeightedChiSquare.weightedChiSq`) with characteristic
function `φ(t) = ∏ⱼ (1 - 2 i λⱼ t)^{-1/2}` (`daviesCharFun`; `charFun_weightedChiSq`),
Gil-Pelaez inversion (`MathlibExt.Analysis.GilPelaez.tendsto_gilPelaez`) gives, for every `q`,
`½ + π⁻¹ ∫₀^T Im(e^{-i t q} φ(t)) / t dt → ½ (P(Q > q) + P(Q ≥ q))` as `T → ∞`.

## Main results

* `tendsto_davies`: the mid-p limit above, for every `q` and every weight vector.
* `weightedChiSq_singleton`: if some `λⱼ ≠ 0`, the law has no atoms.
* `tendsto_davies_of_measure_singleton`, `tendsto_davies_of_ne_zero`: at a point without mass,
  in particular for every `q` when some `λⱼ ≠ 0`, the limit is the upper tail `P(Q > q)`.
* `integrable_id_weightedChiSq`: the law has a finite mean (the hypothesis of Gil-Pelaez).

With all weights zero `Q ≡ 0`, and at `q = 0` the limit is the mid-p value `½`, not
`P(Q > 0) = 0`; that is why `tendsto_davies` states the mid-p limit.

## Source contract

R. B. Davies, *Algorithm AS 155: The distribution of a linear combination of χ² random
variables*, J. R. Stat. Soc. C 29 (1980), 323–333, eq. (1):
`P(Q < c) = ½ - π⁻¹ ∫₀^∞ Im[φ(u) e^{-i u c}] / u du`, stated here as the equivalent upper tail,
in the central case without the extra normal term. Davies' numerical algorithm (discretization
and error bounds) is not formalized.

## Attribution

Moved verbatim (statements and proofs unchanged) from section `Davies` of
`MathlibExt/Biology/StatisticalGenetics/RareVariantInference/BurdenSKATO.lean` (T88, PR #1621),
which now imports this module; only the namespace changed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open MathlibExt.Analysis.GilPelaez MathlibExt.Analysis.WeightedChiSquare

namespace MathlibExt.Probability.Distributions.DaviesFormula

open Real Set Filter Topology

/-- The characteristic function of `∑ⱼ λⱼ χ²₁` used in Davies' formula,
`φ(t) = ∏ⱼ (1 - 2 i λⱼ t)^{-1/2}` (principal branch; each base has real part `1`). -/
noncomputable def daviesCharFun {k : Type*} [Fintype k] (lam : k → ℝ) (t : ℝ) : ℂ :=
  ∏ j, (1 - 2 * lam j * t * Complex.I) ^ (-(1 / 2) : ℂ)

/-- The weighted chi-square law has a finite mean. -/
theorem integrable_id_weightedChiSq {k : Type*} [Fintype k] (lam : k → ℝ) :
    Integrable id (weightedChiSq lam) := by
  have hmap : ∀ j, (Measure.pi fun _ : k => gaussianReal 0 1).map (Function.eval j) =
      gaussianReal 0 1 := fun j =>
    (measurePreserving_eval (fun _ : k => gaussianReal 0 1) j).map_eq
  have hint : ∀ j, Integrable (fun ξ : k → ℝ => ξ j ^ 2)
      (Measure.pi fun _ => gaussianReal 0 1) := by
    intro j
    have h2 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) :=
      (memLp_id_gaussianReal 2).integrable_sq
    rw [← hmap j] at h2
    exact (integrable_map_measure (continuous_pow 2).aestronglyMeasurable
      (measurable_pi_apply j).aemeasurable).1 h2
  rw [weightedChiSq, integrable_map_measure aestronglyMeasurable_id
    (by fun_prop : Measurable fun ξ : k → ℝ => ∑ j, lam j * ξ j ^ 2).aemeasurable]
  exact integrable_finsetSum _ fun j _ => (hint j).const_mul _

/-- **Davies' p-value formula** (Davies 1980, eq. (1), from Gil-Pelaez's inversion theorem).
For `Q ~ ∑ⱼ λⱼ χ²₁` and every `q`,
`½ + π⁻¹ ∫₀^T Im(e^{-i t q} φ(t)) / t dt → ½ (P(Q > q) + P(Q ≥ q))` as `T → ∞`, with
`φ = daviesCharFun λ`. The improper integral is the one Davies' algorithm discretizes. -/
theorem tendsto_davies {k : Type*} [Fintype k] (lam : k → ℝ) (q : ℝ) :
    Tendsto (fun T => 1 / 2 + π⁻¹ * ∫ t in (0 : ℝ)..T,
        (Complex.exp (-(t * q) * Complex.I) * daviesCharFun lam t).im / t) atTop
      (𝓝 (((weightedChiSq lam).real (Ioi q) + (weightedChiSq lam).real (Ici q)) / 2)) := by
  have h := tendsto_gilPelaez (integrable_id_weightedChiSq lam) q
  simp_rw [charFun_weightedChiSq] at h
  exact h

/-- **Davies' formula for the upper tail**: at a point `q` without mass, the limit is the
p-value `P(Q > q)`. -/
theorem tendsto_davies_of_measure_singleton {k : Type*} [Fintype k] (lam : k → ℝ) {q : ℝ}
    (hq : weightedChiSq lam {q} = 0) :
    Tendsto (fun T => 1 / 2 + π⁻¹ * ∫ t in (0 : ℝ)..T,
        (Complex.exp (-(t * q) * Complex.I) * daviesCharFun lam t).im / t) atTop
      (𝓝 ((weightedChiSq lam).real (Ioi q))) := by
  have h := tendsto_davies lam q
  rwa [measureReal_congr (Ioi_ae_eq_Ici' hq).symm, add_self_div_two] at h

/-- **No atoms**: if some weight is nonzero, the weighted chi-square law gives every point
mass `0`. -/
theorem weightedChiSq_singleton {k : Type*} [Fintype k] {lam : k → ℝ} {j : k} (hj : lam j ≠ 0)
    (q : ℝ) : weightedChiSq lam {q} = 0 := by
  classical
  set f : (k → ℝ) → ℝ := fun ξ => ∑ i, lam i * ξ i ^ 2 with hfdef
  have hf : Measurable f := by fun_prop
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : k => ℝ) (· = j)
  have he := measurePreserving_piEquivPiSubtypeProd (fun _ : k => gaussianReal 0 1) (· = j)
  set j0 : {i // i = j} := ⟨j, rfl⟩
  have hpt : ∀ c : ℝ, gaussianReal 0 1 {x | lam j * x ^ 2 = c} = 0 := by
    intro c
    refine measure_mono_null (t := {√(c / lam j), -√(c / lam j)}) (fun x hx => ?_)
      (gaussianReal_absolutelyContinuous 0 one_ne_zero ((Set.toFinite _).measure_zero _))
    have hx : lam j * x ^ 2 = c := hx
    have hx2 : x ^ 2 = c / lam j := by rw [← hx]; field_simp
    have habs : |x| = √(c / lam j) := by rw [← hx2, Real.sqrt_sq_eq_abs]
    rcases (abs_eq (Real.sqrt_nonneg _)).1 habs with h | h <;> simp [h]
  have key : ∀ a b, f (e.symm (a, b)) = lam j * a j0 ^ 2 + f (e.symm (0, b)) := by
    intro a b
    have h : f (e.symm (a, b)) - f (e.symm (0, b)) = lam j * a j0 ^ 2 := by
      simp only [hfdef, ← Finset.sum_sub_distrib]
      rw [Finset.sum_eq_single j]
      · simp [e, MeasurableEquiv.piEquivPiSubtypeProd, j0]
      · intro i _ hi
        simp [e, MeasurableEquiv.piEquivPiSubtypeProd, hi]
      · simp
    linarith
  rw [weightedChiSq, Measure.map_apply hf (measurableSet_singleton q), ← he.symm.map_eq,
    MeasurableEquiv.map_apply,
    Measure.prod_apply_symm (e.symm.measurable (hf (measurableSet_singleton q)))]
  refine (lintegral_congr fun b => ?_).trans lintegral_zero
  have hs : (fun a => (a, b)) ⁻¹' (e.symm ⁻¹' (f ⁻¹' {q})) =
      Function.eval j0 ⁻¹' {x | lam j * x ^ 2 = q - f (e.symm (0, b))} := by
    ext a
    simp only [mem_preimage, mem_singleton_iff, mem_ofPred_eq, Function.eval, key a b]
    constructor <;> intro h <;> linarith
  rw [hs]
  convert ((measurePreserving_eval (fun _ : {i // i = j} => gaussianReal 0 1) j0).measure_preimage
    (s := {x | lam j * x ^ 2 = q - f (e.symm (0, b))})
    (measurableSet_eq_fun (by fun_prop : Measurable fun x : ℝ => lam j * x ^ 2)
      measurable_const).nullMeasurableSet).trans (hpt _)

/-- **Davies' formula, nondegenerate case**: when some weight is nonzero, the limit is the exact
upper tail `P(Q > q)` for every `q`. -/
theorem tendsto_davies_of_ne_zero {k : Type*} [Fintype k] {lam : k → ℝ} {j : k} (hj : lam j ≠ 0)
    (q : ℝ) :
    Tendsto (fun T => 1 / 2 + π⁻¹ * ∫ t in (0 : ℝ)..T,
        (Complex.exp (-(t * q) * Complex.I) * daviesCharFun lam t).im / t) atTop
      (𝓝 ((weightedChiSq lam).real (Ioi q))) :=
  tendsto_davies_of_measure_singleton lam (weightedChiSq_singleton hj q)

end MathlibExt.Probability.Distributions.DaviesFormula

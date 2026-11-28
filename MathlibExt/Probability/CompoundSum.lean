/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.IdentDistribIndep
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Moments of a compound sum

An independent count and severity sequence have the same joint law as copies on separate
coordinates of a product space. There, integrating first over the severities leaves an
ordinary integral over the count. The fixed-length second moment is quadratic in the count,
so a second moment of the count suffices even when its support is unbounded.

The mean and variance formulas appear in R. Kaas, M. Goovaerts, J. Dhaene and M. Denuit,
*Modern Actuarial Risk Theory*,
[recap of chapters 1–6](https://www1feb-uva.nl/ke/act/people/kaas/Recap123456.pdf),
p. 1, right column, “Collective model”.
-/

public section

open MeasureTheory ProbabilityTheory

namespace MathlibExt.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

private theorem identDistrib_compoundSum_prod {N : Ω → ℕ} {X : ℕ → Ω → ℝ}
    (hN : AEMeasurable N P) (hX : ∀ i, AEMeasurable (X i) P)
    (hNX : IndepFun N (fun ω i ↦ X i ω) P) :
    IdentDistrib (fun ω ↦ ∑ i ∈ Finset.range (N ω), X i ω)
      (fun z : Ω × Ω ↦ ∑ i ∈ Finset.range (N z.1), X i z.2) P (P.prod P) := by
  have hseq : AEMeasurable (fun ω i ↦ X i ω) P := .of_eval hX
  have hfst := (hasLaw_map hN).identDistrib ((hasLaw_map hN).comp
    (measurePreserving_fst : MeasurePreserving _ (P.prod P) P).hasLaw)
  have hsnd := (hasLaw_map hseq).identDistrib ((hasLaw_map hseq).comp
    (measurePreserving_snd : MeasurePreserving _ (P.prod P) P).hasLaw)
  have hpair := hfst.prodMk hsnd hNX (indepFun_prod₀ hN hseq)
  exact hpair.comp (u := fun z : ℕ × (ℕ → ℝ) ↦ ∑ i ∈ Finset.range z.1, z.2 i)
    (measurable_from_prod_countable_right fun n ↦
      Finset.measurable_sum (Finset.range n) fun i _ ↦ (measurable_pi_apply i :
        Measurable fun x : ℕ → ℝ ↦ x i))

/-- For a natural-valued count `N` independent of the whole i.i.d. severity sequence `X`,
assume the real count and the first severity are square integrable. The sum `S` of the first
`N` severities (zero if `N = 0`) is square integrable, with mean `E[N] E[X₀]` and variance
`E[N] Var(X₀) + Var(N) E[X₀]²`. The severities may be signed and the count need not be bounded. -/
theorem compoundSum_moments {N : Ω → ℕ} {X : ℕ → Ω → ℝ}
    (hN : AEMeasurable N P) (hN₂ : MemLp (fun ω ↦ (N ω : ℝ)) 2 P)
    (hX₂ : MemLp (X 0) 2 P) (hiid : iIndepFun X P)
    (hid : ∀ i, IdentDistrib (X i) (X 0) P P) (hNX : IndepFun N (fun ω i ↦ X i ω) P) :
    let S := fun ω ↦ ∑ i ∈ Finset.range (N ω), X i ω
    MemLp S 2 P ∧ P[S] = P[fun ω ↦ (N ω : ℝ)] * P[X 0] ∧
      variance S P = P[fun ω ↦ (N ω : ℝ)] * variance (X 0) P +
        variance (fun ω ↦ (N ω : ℝ)) P * P[X 0] ^ 2 := by
  let T (n : ℕ) (ω : Ω) := ∑ i ∈ Finset.range n, X i ω
  have hXi (i : ℕ) := (hid i).memLp_iff.mpr hX₂
  have hT (n : ℕ) : MemLp (T n) 2 P := memLp_finsetSum _ fun i _ ↦ hXi i
  have hmean (n : ℕ) : P[T n] = (n : ℝ) * P[X 0] := by
    calc
      _ = ∑ i ∈ Finset.range n, P[X i] :=
        integral_finsetSum (f := X) _ fun i _ ↦ (hXi i).integrable one_le_two
      _ = _ := by simp [fun i ↦ (hid i).integral_eq, nsmul_eq_mul]
  have hraw (n : ℕ) : (∫ ω, (T n ω) ^ 2 ∂P) = n * variance (X 0) P + n ^ 2 * P[X 0] ^ 2 := by
    have hv : variance (T n) P = n * variance (X 0) P := by
      have heq : T n = ∑ i ∈ Finset.range n, X i := by ext ω; simp [T]
      rw [heq, IndepFun.variance_sum (fun i _ ↦ hXi i) (fun i _ j _ hij ↦ hiid.indepFun hij)]
      simp [fun i ↦ (hid i).variance_eq, nsmul_eq_mul]
    rw [variance_eq_sub (hT n), hmean] at hv
    change (∫ ω, (T n ω) ^ 2 ∂P) - ((n : ℝ) * P[X 0]) ^ 2 = _ at hv
    linear_combination hv
  let U (z : Ω × Ω) := T (N z.1) z.2
  have hlaw := identDistrib_compoundSum_prod hN (fun i ↦ (hXi i).aemeasurable) hNX
  have hmU : AEStronglyMeasurable U (P.prod P) := hlaw.aemeasurable_snd.aestronglyMeasurable
  have h₁ := (hN₂.integrable one_le_two).mul_const (variance (X 0) P)
  have h₂ := hN₂.integrable_sq.mul_const (P[X 0] ^ 2)
  have hUsq : Integrable (fun z ↦ U z ^ 2) (P.prod P) := by
    apply (integrable_prod_iff (hmU.pow 2)).2
    refine ⟨.of_forall fun ω ↦ (hT (N ω)).integrable_sq, ?_⟩
    change Integrable (fun x ↦ ∫ y, ‖T (N x) y ^ 2‖ ∂P) P
    simpa only [Real.norm_eq_abs, abs_sq, hraw, Pi.add_def] using h₁.add h₂
  have hU := (memLp_two_iff_integrable_sq hmU).2 hUsq
  have hEU : (∫ z, U z ∂P.prod P) = P[fun ω ↦ (N ω : ℝ)] * P[X 0] := by
    rw [integral_prod _ (hU.integrable one_le_two)]
    simp only [U, hmean, integral_mul_const]
  refine ⟨hlaw.memLp_iff.mpr hU, hlaw.integral_eq.trans hEU, hlaw.variance_eq.trans ?_⟩
  rw [variance_eq_sub hU, variance_eq_sub hN₂]
  change (∫ z, U z ^ 2 ∂P.prod P) - (∫ z, U z ∂P.prod P) ^ 2 = _
  rw [integral_prod _ hUsq, hEU]
  simp only [U, hraw, integral_add h₁ h₂, integral_mul_const, Pi.pow_apply]
  ring

end MathlibExt.Probability

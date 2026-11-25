/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.OptimalTransport.Kantorovich
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.Topology.MetricSpace.ThickenedIndicator
public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

/-!
# Wasserstein distances

For a (pseudo-)extended metric space `X` with its Borel σ-algebra and `p ∈ [1, ∞)`, the
Wasserstein distance of order `p` between probability measures `μ, ν` on `X` is
`W_p(μ, ν) = (inf_π ∫ d(x, y)^p dπ(x, y))^(1/p)`, the infimum running over the couplings `π` of
`μ` and `ν` (C. Villani, *Optimal Transport: Old and New*, Springer 2009, Definition 6.1).
It takes values in `[0, ∞]`.

Main results, following the proof that `W_p` satisfies the axioms of a distance after
Definition 6.1 of Villani's book:

* `wasserstein_comm`: symmetry;
* `wasserstein_self`: `W_p(μ, μ) = 0`;
* `wasserstein_dirac`: `W_p(δ_x, δ_y) = d(x, y)` (Example 6.3);
* `exists_gluing`: the gluing lemma for couplings (Villani, Chapter 1);
* `wasserstein_triangle`: the triangle inequality, from gluing and Minkowski's inequality;
* `wasserstein_mono`: `W_p ≤ W_q` for `0 < p ≤ q` (Remark 6.6);
* `wasserstein_lt_top`: `W_p` is finite on measures with finite `p`-th moments (Definition 6.4);
* `lintegral_le_add_mul_wasserstein_one`: the elementary half of the Kantorovich–Rubinstein
  formula (Remark 6.5) for nonnegative Lipschitz test functions;
* `eq_of_wasserstein_eq_zero`: `W_p(μ, ν) = 0` forces `μ = ν`.

Couplings are `MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted.IsCoupling`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

open MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted (IsCoupling)

namespace MathlibExt.MeasureTheory.OptimalTransport.Wasserstein

section Gluing

/-- **Gluing lemma.** Let `π₁₂` be a probability measure on `X₁ × X₂` and `π₂₃` a probability
measure on `X₂ × X₃` such that the second marginal of `π₁₂` equals the first marginal of `π₂₃`.
If `X₃` is a standard Borel space, there is a probability measure `π` on `(X₁ × X₂) × X₃` whose
marginal on `X₁ × X₂` is `π₁₂` and whose marginal on `X₂ × X₃` is `π₂₃`
(C. Villani, *Optimal Transport: Old and New*, Springer 2009, Chapter 1, "Gluing lemma";
there the three spaces are Polish). -/
theorem exists_gluing {X₁ X₂ X₃ : Type*} [MeasurableSpace X₁] [MeasurableSpace X₂]
    [MeasurableSpace X₃] [StandardBorelSpace X₃]
    (π₁₂ : Measure (X₁ × X₂)) (π₂₃ : Measure (X₂ × X₃))
    [IsProbabilityMeasure π₁₂] [IsProbabilityMeasure π₂₃]
    (h : π₁₂.map Prod.snd = π₂₃.map Prod.fst) :
    ∃ π : Measure ((X₁ × X₂) × X₃), IsProbabilityMeasure π ∧
      π.map Prod.fst = π₁₂ ∧ π.map (fun z => (z.1.2, z.2)) = π₂₃ := by
  have : Nonempty X₃ := nonempty_of_isProbabilityMeasure (π₂₃.map Prod.snd)
  set κ := π₂₃.condKernel
  set κ' := κ.comap Prod.snd measurable_snd
  refine ⟨π₁₂ ⊗ₘ κ', inferInstance, ?_, ?_⟩
  · exact Measure.fst_compProd π₁₂ κ'
  · ext s hs
    have hg : Measurable (fun z : (X₁ × X₂) × X₃ => (z.1.2, z.2)) := by fun_prop
    rw [Measure.map_apply hg hs, Measure.compProd_apply (hg hs)]
    conv_rhs => rw [← Measure.disintegrate π₂₃ π₂₃.condKernel]
    rw [Measure.compProd_apply hs, Measure.fst, ← h,
      lintegral_map (Kernel.measurable_kernel_prodMk_left hs) measurable_snd]
    rfl

end Gluing

variable {X : Type*} [PseudoEMetricSpace X] [MeasurableSpace X]

/-- **Optimal transport cost of order `p`.** For probability measures `μ` and `ν` on a
(pseudo-)extended metric space `X`, `transportCost p μ ν` is the infimum of
`∫ d(x, y)^p dπ(x, y)` over all couplings `π` of `μ` and `ν`, a value in `[0, ∞]`
(C. Villani, *Optimal Transport: Old and New*, Springer 2009, equation (6.2) before taking the
`1/p`-th power). -/
noncomputable def transportCost (p : ℝ) (μ ν : ProbabilityMeasure X) : ℝ≥0∞ :=
  ⨅ (π : ProbabilityMeasure (X × X)) (_ : IsCoupling μ ν π),
    ∫⁻ z, edist z.1 z.2 ^ p ∂(π : Measure (X × X))

/-- **Wasserstein distance of order `p`.** For probability measures `μ` and `ν` on a
(pseudo-)extended metric space `X`, `W_p(μ, ν) = (inf_π ∫ d(x, y)^p dπ(x, y))^(1/p)`, the
infimum over the couplings `π` of `μ` and `ν`, with values in `[0, ∞]`
(C. Villani, *Optimal Transport: Old and New*, Springer 2009, Definition 6.1, where `X` is a
Polish metric space and `p ∈ [1, ∞)`; `W_1` is the Kantorovich–Rubinstein distance, Particular
Case 6.2). -/
noncomputable def wasserstein (p : ℝ) (μ ν : ProbabilityMeasure X) : ℝ≥0∞ :=
  transportCost p μ ν ^ (1 / p)

/-- **The product coupling.** The product `μ ⊗ ν` of two probability measures is a coupling of
`μ` and `ν` (C. Villani, *Optimal Transport: Old and New*, Springer 2009, Chapter 1: the trivial
coupling, which makes the set of couplings nonempty). -/
theorem isCoupling_prod {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : ProbabilityMeasure Y) (ν : ProbabilityMeasure Z) :
    IsCoupling μ ν (μ.prod ν) := by
  refine ⟨?_, ?_⟩
  · have h2 := congrArg (fun π : ProbabilityMeasure Y => (π : Measure Y))
      (ProbabilityMeasure.map_fst_prod μ ν)
    rw [ProbabilityMeasure.toMeasure_map] at h2
    exact h2.symm
  · have h2 := congrArg (fun π : ProbabilityMeasure Z => (π : Measure Z))
      (ProbabilityMeasure.map_snd_prod μ ν)
    rw [ProbabilityMeasure.toMeasure_map] at h2
    exact h2.symm

/-- **Swapped coupling.** Swapping the coordinates of a coupling of `μ` and `ν` gives a coupling
of `ν` and `μ` (C. Villani, *Optimal Transport: Old and New*, Springer 2009, proof of the
symmetry of `W_p` after Definition 6.1). -/
theorem isCoupling_swap {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    {μ : ProbabilityMeasure Y} {ν : ProbabilityMeasure Z} {π : ProbabilityMeasure (Y × Z)}
    (h : IsCoupling μ ν π) :
    IsCoupling ν μ (π.map Prod.swap) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rw [ProbabilityMeasure.toMeasure_map, Measure.map_map measurable_fst measurable_swap]
    exact h2
  · rw [ProbabilityMeasure.toMeasure_map, Measure.map_map measurable_snd measurable_swap]
    exact h1

/-- **Diagonal coupling.** The image of `μ` under the diagonal map `x ↦ (x, x)` is a coupling of
`μ` with itself (C. Villani, *Optimal Transport: Old and New*, Springer 2009, Definition 1.2:
the deterministic coupling given by the identity map). -/
theorem isCoupling_diag {Y : Type*} [MeasurableSpace Y] (μ : ProbabilityMeasure Y) :
    IsCoupling μ μ (μ.map (fun x => (x, x))) := by
  have hd : Measurable (fun x : Y => (x, x)) := by fun_prop
  refine ⟨?_, ?_⟩
  · rw [ProbabilityMeasure.toMeasure_map, Measure.map_map measurable_fst hd]
    exact (Measure.map_id).symm
  · rw [ProbabilityMeasure.toMeasure_map, Measure.map_map measurable_snd hd]
    exact (Measure.map_id).symm

/-- **Every coupling bounds the transport cost.** `transportCost p μ ν ≤ ∫ d^p dπ` for every
coupling `π` of `μ` and `ν`; this is the defining property of the infimum in Villani's
equation (6.2). -/
theorem transportCost_le_of_isCoupling {p : ℝ} {μ ν : ProbabilityMeasure X}
    {π : ProbabilityMeasure (X × X)} (h : IsCoupling μ ν π) :
    transportCost p μ ν ≤ ∫⁻ z, edist z.1 z.2 ^ p ∂(π : Measure (X × X)) :=
  iInf₂_le π h

/-- **Every coupling bounds the Wasserstein distance.** For `p ≥ 0`, `W_p(μ, ν)` is at most
`(∫ d^p dπ)^(1/p)` for every coupling `π` of `μ` and `ν` (C. Villani, *Optimal Transport: Old
and New*, Springer 2009, Definition 6.1). -/
theorem wasserstein_le_of_isCoupling {p : ℝ} (hp : 0 ≤ p) {μ ν : ProbabilityMeasure X}
    {π : ProbabilityMeasure (X × X)} (h : IsCoupling μ ν π) :
    wasserstein p μ ν ≤ (∫⁻ z, edist z.1 z.2 ^ p ∂(π : Measure (X × X))) ^ (1 / p) :=
  ENNReal.rpow_le_rpow (transportCost_le_of_isCoupling h) (by positivity)

private theorem iInf_rpow {ι : Sort*} (f : ι → ℝ≥0∞) {r : ℝ} (hr : 0 < r) :
    (⨅ i, f i) ^ r = ⨅ i, f i ^ r := by
  simpa only [ENNReal.orderIsoRpow_apply] using (ENNReal.orderIsoRpow r hr).map_iInf f

/-- **Wasserstein distance as an infimum over couplings.** For `p > 0`, `W_p(μ, ν)` is the
infimum over couplings `π` of `μ` and `ν` of `(∫ d^p dπ)^(1/p)`: the `1/p`-th power commutes
with the infimum (C. Villani, *Optimal Transport: Old and New*, Springer 2009, second form of
equation (6.2)). -/
theorem wasserstein_eq_iInf {p : ℝ} (hp : 0 < p) (μ ν : ProbabilityMeasure X) :
    wasserstein p μ ν = ⨅ (π : ProbabilityMeasure (X × X)) (_ : IsCoupling μ ν π),
      (∫⁻ z, edist z.1 z.2 ^ p ∂(π : Measure (X × X))) ^ (1 / p) := by
  rw [wasserstein, transportCost, iInf_rpow _ (one_div_pos.2 hp)]
  congr 1
  ext π
  exact iInf_rpow _ (one_div_pos.2 hp)

/-- **Symmetry of the Wasserstein distance.** `W_p(μ, ν) = W_p(ν, μ)`
(C. Villani, *Optimal Transport: Old and New*, Springer 2009, proof that `W_p` satisfies the
axioms of a distance, after Definition 6.1). -/
theorem wasserstein_comm [OpensMeasurableSpace X] [SecondCountableTopology X]
    (p : ℝ) (μ ν : ProbabilityMeasure X) :
    wasserstein p μ ν = wasserstein p ν μ := by
  have key : ∀ μ ν : ProbabilityMeasure X, transportCost p ν μ ≤ transportCost p μ ν := by
    intro μ ν
    refine le_iInf₂ fun π hπ => (transportCost_le_of_isCoupling (isCoupling_swap hπ)).trans_eq ?_
    rw [ProbabilityMeasure.toMeasure_map,
      lintegral_map (measurable_edist.pow_const p) measurable_swap]
    simp only [Prod.fst_swap, Prod.snd_swap, edist_comm]
  rw [wasserstein, wasserstein, le_antisymm (key ν μ) (key μ ν)]

/-- **The Wasserstein distance vanishes on the diagonal.** For `p > 0`, `W_p(μ, μ) = 0`
(C. Villani, *Optimal Transport: Old and New*, Springer 2009, proof that `W_p` satisfies the
axioms of a distance, after Definition 6.1). -/
theorem wasserstein_self [OpensMeasurableSpace X] [SecondCountableTopology X] {p : ℝ}
    (hp : 0 < p) (μ : ProbabilityMeasure X) :
    wasserstein p μ μ = 0 := by
  refine le_antisymm ((wasserstein_le_of_isCoupling hp.le (isCoupling_diag μ)).trans_eq ?_)
    bot_le
  have hd : Measurable (fun x : X => (x, x)) := by fun_prop
  rw [ProbabilityMeasure.toMeasure_map,
    lintegral_map (measurable_edist.pow_const p) hd]
  simp [ENNReal.zero_rpow_of_pos hp, hp]

/-- **Wasserstein distance between Dirac masses.** For `p > 0`, `W_p(δ_x, δ_y) = d(x, y)`
(C. Villani, *Optimal Transport: Old and New*, Springer 2009, Example 6.3). -/
theorem wasserstein_dirac {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {p : ℝ} (hp : 0 < p) (x y : X) :
    wasserstein p ⟨Measure.dirac x, inferInstance⟩ ⟨Measure.dirac y, inferInstance⟩ =
      edist x y := by
  set δx : ProbabilityMeasure X := ⟨Measure.dirac x, inferInstance⟩
  set δy : ProbabilityMeasure X := ⟨Measure.dirac y, inferInstance⟩
  have hcost : ∀ π : ProbabilityMeasure (X × X), IsCoupling δx δy π →
      ∫⁻ z, edist z.1 z.2 ^ p ∂(π : Measure (X × X)) = edist x y ^ p := by
    intro π ⟨h1, h2⟩
    have hae : ∀ᵐ z ∂(π : Measure (X × X)), z.1 = x ∧ z.2 = y := by
      have e1 : ∀ᵐ z ∂(π : Measure (X × X)), z.1 = x := by
        have : ∀ᵐ w ∂((π : Measure (X × X)).map Prod.fst), w = x := by
          rw [← h1]; change ∀ᵐ w ∂(Measure.dirac x), w = x; rw [ae_dirac_eq]; exact rfl
        exact ae_of_ae_map measurable_fst.aemeasurable this
      have e2 : ∀ᵐ z ∂(π : Measure (X × X)), z.2 = y := by
        have : ∀ᵐ w ∂((π : Measure (X × X)).map Prod.snd), w = y := by
          rw [← h2]; change ∀ᵐ w ∂(Measure.dirac y), w = y; rw [ae_dirac_eq]; exact rfl
        exact ae_of_ae_map measurable_snd.aemeasurable this
      filter_upwards [e1, e2] with z hz1 hz2 using ⟨hz1, hz2⟩
    rw [lintegral_congr_ae (g := fun _ => edist x y ^ p)
      (hae.mono fun z hz => by simp only [hz.1, hz.2])]
    simp
  have hT : transportCost p δx δy = edist x y ^ p := by
    refine le_antisymm ((transportCost_le_of_isCoupling (isCoupling_prod δx δy)).trans_eq
      (hcost _ (isCoupling_prod δx δy))) (le_iInf₂ fun π hπ => (hcost π hπ).ge)
  rw [wasserstein, hT, ← ENNReal.rpow_mul, mul_one_div_cancel hp.ne', ENNReal.rpow_one]

/-- **Triangle inequality for the Wasserstein distance.** On a standard Borel
(pseudo-)extended metric space, for `p ≥ 1`, `W_p(μ₁, μ₃) ≤ W_p(μ₁, μ₂) + W_p(μ₂, μ₃)`
(C. Villani, *Optimal Transport: Old and New*, Springer 2009, proof that `W_p` satisfies the
axioms of a distance, after Definition 6.1: gluing lemma plus Minkowski's inequality; there
optimal couplings are glued, here arbitrary ones, which avoids the existence theorem). -/
theorem wasserstein_triangle [BorelSpace X] [SecondCountableTopology X]
    [StandardBorelSpace X] {p : ℝ} (hp : 1 ≤ p) (μ₁ μ₂ μ₃ : ProbabilityMeasure X) :
    wasserstein p μ₁ μ₃ ≤ wasserstein p μ₁ μ₂ + wasserstein p μ₂ μ₃ := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  rw [wasserstein_eq_iInf hp0 μ₁ μ₂, wasserstein_eq_iInf hp0 μ₂ μ₃]
  simp only [ENNReal.iInf_add, ENNReal.add_iInf]
  refine le_iInf₂ fun π₂₃ h₂₃ => le_iInf₂ fun π₁₂ h₁₂ => ?_
  have hmid : (π₁₂ : Measure (X × X)).map Prod.snd = (π₂₃ : Measure (X × X)).map Prod.fst :=
    h₁₂.2.symm.trans h₂₃.1
  obtain ⟨π, hπP, hπ1, hπ2⟩ := exists_gluing (π₁₂ : Measure (X × X)) (π₂₃ : Measure (X × X)) hmid
  have hg : Measurable (fun z : (X × X) × X => (z.1.1, z.2)) := by fun_prop
  let π₁₃ : ProbabilityMeasure (X × X) := ⟨π.map (fun z => (z.1.1, z.2)), inferInstance⟩
  have h₁₃ : IsCoupling μ₁ μ₃ π₁₃ := by
    refine ⟨?_, ?_⟩
    · change (μ₁ : Measure X) = (π.map (fun z => (z.1.1, z.2))).map Prod.fst
      rw [Measure.map_map measurable_fst hg, h₁₂.1, ← hπ1,
        Measure.map_map measurable_fst measurable_fst]
      rfl
    · change (μ₃ : Measure X) = (π.map (fun z => (z.1.1, z.2))).map Prod.snd
      have hg2 : Measurable (fun z : (X × X) × X => (z.1.2, z.2)) := by fun_prop
      rw [Measure.map_map measurable_snd hg, h₂₃.2, ← hπ2,
        Measure.map_map measurable_snd hg2]
      rfl
  refine (wasserstein_le_of_isCoupling hp0.le h₁₃).trans ?_
  have hd : Measurable (fun z : X × X => edist z.1 z.2 ^ p) := measurable_edist.pow_const p
  have e13 : ∫⁻ z, edist z.1 z.2 ^ p ∂(π₁₃ : Measure (X × X)) =
      ∫⁻ z, edist z.1.1 z.2 ^ p ∂π := lintegral_map hd hg
  have e12 : ∫⁻ z, edist z.1 z.2 ^ p ∂(π₁₂ : Measure (X × X)) =
      ∫⁻ z, edist z.1.1 z.1.2 ^ p ∂π := by
    rw [← hπ1, lintegral_map hd measurable_fst]
  have e23 : ∫⁻ z, edist z.1 z.2 ^ p ∂(π₂₃ : Measure (X × X)) =
      ∫⁻ z, edist z.1.2 z.2 ^ p ∂π := by
    rw [← hπ2, lintegral_map hd (by fun_prop)]
  rw [e13, e12, e23]
  have hf : AEMeasurable (fun z : (X × X) × X => edist z.1.1 z.1.2) π :=
    (measurable_edist.comp measurable_fst).aemeasurable
  have hg' : AEMeasurable (fun z : (X × X) × X => edist z.1.2 z.2) π :=
    (measurable_edist.comp (by fun_prop : Measurable fun z : (X × X) × X => (z.1.2, z.2)))
      |>.aemeasurable
  refine le_trans ?_ (ENNReal.lintegral_Lp_add_le hf hg' hp)
  gcongr with z
  exact edist_triangle _ _ _

/-- **Monotonicity of the Wasserstein distances in the exponent.** For `0 < p ≤ q`,
`W_p(μ, ν) ≤ W_q(μ, ν)` (C. Villani, *Optimal Transport: Old and New*, Springer 2009,
Remark 6.6, inequality (6.4)). -/
theorem wasserstein_mono [OpensMeasurableSpace X] [SecondCountableTopology X]
    {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) (μ ν : ProbabilityMeasure X) :
    wasserstein p μ ν ≤ wasserstein q μ ν := by
  rw [wasserstein_eq_iInf hp, wasserstein_eq_iInf (hp.trans_le hpq)]
  refine iInf₂_mono fun π _ => ?_
  have h := eLpNorm'_le_eLpNorm'_of_exponent_le (f := fun z : X × X => edist z.1 z.2) hp hpq
    (π : Measure (X × X)) measurable_edist.aestronglyMeasurable
  simpa only [eLpNorm', enorm_eq_self] using h

/-- **The Wasserstein distance is finite on measures with finite `p`-th moments.** For `p ≥ 1`
and `x₀ ∈ X`, if `∫ d(x₀, x)^p dμ` and `∫ d(x₀, y)^p dν` are finite then `W_p(μ, ν) < ∞`: the
product coupling has cost at most `2^(p-1) (∫ d(x₀, x)^p dμ + ∫ d(x₀, y)^p dν)`
(C. Villani, *Optimal Transport: Old and New*, Springer 2009, Definition 6.4 and the proof that
`W_p` is finite on `P_p` that follows it). -/
theorem wasserstein_lt_top [OpensMeasurableSpace X] [SecondCountableTopology X]
    {p : ℝ} (hp : 1 ≤ p) (x₀ : X) {μ ν : ProbabilityMeasure X}
    (hμ : ∫⁻ x, edist x₀ x ^ p ∂(μ : Measure X) < ⊤)
    (hν : ∫⁻ y, edist x₀ y ^ p ∂(ν : Measure X) < ⊤) :
    wasserstein p μ ν < ⊤ := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hm : Measurable fun x : X => edist x₀ x ^ p :=
    (measurable_const.edist measurable_id).pow_const p
  obtain ⟨h1, h2⟩ := isCoupling_prod μ ν
  have hcost : ∫⁻ z, edist z.1 z.2 ^ p ∂((μ.prod ν : ProbabilityMeasure (X × X)) : Measure (X × X))
      ≤ 2 ^ (p - 1) * (∫⁻ x, edist x₀ x ^ p ∂(μ : Measure X) +
        ∫⁻ y, edist x₀ y ^ p ∂(ν : Measure X)) := by
    calc ∫⁻ z, edist z.1 z.2 ^ p ∂((μ.prod ν : ProbabilityMeasure (X × X)) : Measure (X × X))
        ≤ ∫⁻ z, 2 ^ (p - 1) * (edist x₀ z.1 ^ p + edist x₀ z.2 ^ p)
            ∂((μ.prod ν : ProbabilityMeasure (X × X)) : Measure (X × X)) := by
          refine lintegral_mono fun z => ?_
          calc edist z.1 z.2 ^ p ≤ (edist x₀ z.1 + edist x₀ z.2) ^ p := by
                gcongr
                calc edist z.1 z.2 ≤ edist z.1 x₀ + edist x₀ z.2 := edist_triangle _ _ _
                  _ = edist x₀ z.1 + edist x₀ z.2 := by rw [edist_comm]
            _ ≤ 2 ^ (p - 1) * (edist x₀ z.1 ^ p + edist x₀ z.2 ^ p) :=
                ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hp
      _ = 2 ^ (p - 1) * (∫⁻ x, edist x₀ x ^ p ∂(μ : Measure X) +
            ∫⁻ y, edist x₀ y ^ p ∂(ν : Measure X)) := by
          have hm1 : Measurable fun z : X × X => edist x₀ z.1 ^ p := hm.comp measurable_fst
          have hm2 : Measurable fun z : X × X => edist x₀ z.2 ^ p := hm.comp measurable_snd
          have hm12 : Measurable fun z : X × X => edist x₀ z.1 ^ p + edist x₀ z.2 ^ p :=
            hm1.add hm2
          rw [lintegral_const_mul _ hm12, lintegral_add_left hm1, h1, h2,
            lintegral_map hm measurable_fst, lintegral_map hm measurable_snd]
  have hT : transportCost p μ ν < ⊤ := by
    refine (transportCost_le_of_isCoupling (isCoupling_prod μ ν)).trans_lt
      (hcost.trans_lt ?_)
    refine ENNReal.mul_lt_top ?_ (ENNReal.add_lt_top.2 ⟨hμ, hν⟩)
    exact ENNReal.rpow_lt_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top
  exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hT.ne

/-- **Lipschitz test functions are controlled by `W_1`.** If `g : X → ℝ≥0` is `K`-Lipschitz,
then `∫ g dμ ≤ ∫ g dν + K W_1(μ, ν)`. This is the elementary inequality behind the
Kantorovich–Rubinstein formula `W_1(μ, ν) = sup_{‖ψ‖_Lip ≤ 1} (∫ ψ dμ - ∫ ψ dν)`
(C. Villani, *Optimal Transport: Old and New*, Springer 2009, Remark 6.5, formula (6.3)). -/
theorem lintegral_le_add_mul_wasserstein_one [OpensMeasurableSpace X]
    [SecondCountableTopology X] {g : X → ℝ≥0} {K : ℝ≥0} (hg : LipschitzWith K g)
    (μ ν : ProbabilityMeasure X) :
    ∫⁻ x, g x ∂(μ : Measure X) ≤ ∫⁻ x, g x ∂(ν : Measure X) + K * wasserstein 1 μ ν := by
  have hgm : Measurable fun x => (g x : ℝ≥0∞) :=
    measurable_coe_nnreal_ennreal.comp hg.continuous.measurable
  simp only [wasserstein, transportCost, div_one, ENNReal.rpow_one]
  have : Nonempty {π : ProbabilityMeasure (X × X) // IsCoupling μ ν π} :=
    ⟨⟨μ.prod ν, isCoupling_prod μ ν⟩⟩
  rw [iInf_subtype', ENNReal.mul_iInf (by simp), ENNReal.add_iInf]
  refine le_iInf fun ⟨π, h1, h2⟩ => ?_
  have hpt : ∀ z : X × X, (g z.1 : ℝ≥0∞) ≤ g z.2 + K * edist z.1 z.2 := by
    intro z
    have hl := hg.edist_le_mul z.1 z.2
    have hle : (g z.1 : ℝ≥0∞) ≤ g z.2 + edist (g z.1) (g z.2) := by
      rw [edist_nndist, ← ENNReal.coe_add, ENNReal.coe_le_coe]
      have := dist_triangle (g z.1 : ℝ) (g z.2) 0
      have h0 : (g z.1 : ℝ) ≤ g z.2 + dist (g z.1 : ℝ) (g z.2) := by
        have := le_abs_self ((g z.1 : ℝ) - g z.2)
        rw [Real.dist_eq]; linarith
      exact_mod_cast h0
    exact hle.trans (by gcongr)
  calc ∫⁻ x, g x ∂(μ : Measure X)
      = ∫⁻ z, g z.1 ∂(π : Measure (X × X)) := by rw [h1, lintegral_map hgm measurable_fst]
    _ ≤ ∫⁻ z, (g z.2 + K * edist z.1 z.2) ∂(π : Measure (X × X)) := lintegral_mono hpt
    _ = ∫⁻ z, g z.2 ∂(π : Measure (X × X)) + K * ∫⁻ z, edist z.1 z.2 ∂(π : Measure (X × X)) := by
        have hgm2 : Measurable fun z : X × X => (g z.2 : ℝ≥0∞) := hgm.comp measurable_snd
        rw [lintegral_add_left hgm2,
          lintegral_const_mul _ measurable_edist]
    _ = ∫⁻ x, g x ∂(ν : Measure X) + K * ∫⁻ z, edist z.1 z.2 ∂(π : Measure (X × X)) := by
        rw [h2, lintegral_map hgm measurable_snd]

/-- **The Wasserstein distance separates probability measures.** On a (pseudo-)extended metric
space with its Borel σ-algebra, for `p ≥ 1`, `W_p(μ, ν) = 0` implies `μ = ν`
(C. Villani, *Optimal Transport: Old and New*, Springer 2009, proof that `W_p` satisfies the
axioms of a distance, after Definition 6.1; here via Lipschitz thickened indicators of closed
sets instead of an optimal coupling). -/
theorem eq_of_wasserstein_eq_zero [BorelSpace X] [SecondCountableTopology X]
    {p : ℝ} (hp : 1 ≤ p) {μ ν : ProbabilityMeasure X} (h : wasserstein p μ ν = 0) :
    μ = ν := by
  have h1 : wasserstein 1 μ ν = 0 :=
    le_antisymm ((wasserstein_mono one_pos hp μ ν).trans h.le) bot_le
  have h1' : wasserstein 1 ν μ = 0 := by rw [wasserstein_comm, h1]
  have hthick : ∀ {δ : ℝ} (hδ : 0 < δ) (F : Set X),
      ∫⁻ x, thickenedIndicator hδ F x ∂(μ : Measure X) =
        ∫⁻ x, thickenedIndicator hδ F x ∂(ν : Measure X) := by
    intro δ hδ F
    have hL := lipschitzWith_thickenedIndicator hδ F
    refine le_antisymm ?_ ?_
    · simpa [h1] using lintegral_le_add_mul_wasserstein_one hL μ ν
    · simpa [h1'] using lintegral_le_add_mul_wasserstein_one hL ν μ
  have hclosed : ∀ F : Set X, IsClosed F → (μ : Measure X) F = (ν : Measure X) F := by
    intro F hF
    have hδ : ∀ n : ℕ, (0 : ℝ) < 1 / (n + 1) := fun n => Nat.one_div_pos_of_nat
    have hlim : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have tμ := tendsto_lintegral_thickenedIndicator_of_isClosed (μ : Measure X) hF hδ hlim
    have tν := tendsto_lintegral_thickenedIndicator_of_isClosed (ν : Measure X) hF hδ hlim
    simp_rw [hthick] at tμ
    exact tendsto_nhds_unique tμ tν
  apply Subtype.ext
  change (μ : Measure X) = ν
  apply ext_of_generate_finite _ ?_ isPiSystem_isClosed
  · exact fun F hF => hclosed F hF
  · exact hclosed Set.univ isClosed_univ
  · rw [BorelSpace.measurable_eq (α := X), borel_eq_generateFrom_isClosed]

end MathlibExt.MeasureTheory.OptimalTransport.Wasserstein

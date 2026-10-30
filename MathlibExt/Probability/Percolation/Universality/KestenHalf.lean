/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.Universality.Defs
public import MathlibExt.Probability.Percolation.Universality.DualConfigLaw

/-!
# Kesten's theorem `p_c = 1/2`, conditional on its analytic inputs

Bond percolation on `ℤ²` at density `1/2` is self-dual: the rotated complement configuration
`dualConfig` has the same law (`dualConfig_preserves_half`). Consequently an event whose complement
is its own preimage under a `ℙ_{1/2}`-preserving map `R ∘ dualConfig` has probability exactly `1/2`
(`half_crossingProb_of_selfDual_dichotomy`). This file combines that computation with two assumed
inputs to obtain `p_c(ℤ²) = 1/2`:

* `θ(1/2) = 0` (Harris), assumed in the form `hCorLowerBound : BoxCrossingProperty ℙ_{1/2} ρ →
  θ(1/2) = 0` together with `hbxp`; it gives `1/2 ≤ p_c`.
* crossing probabilities of the self-dual family tend to `0` for every `p < p_c`
  (`hSharpThreshold`); with the self-duality computation it gives `p_c ≤ 1/2`.

So `kesten_pc_eq_half_of_bxp` is a conditional form of Kesten's theorem: the self-duality step and
the order-theoretic assembly are proved; Harris's theorem, the subcritical decay of crossings, and
the existence of an exactly self-dual crossing family are hypotheses.

## Main definitions

* `StatMech.Universality.halfMeasure`: the Bernoulli bond measure `ℙ_{1/2}` on `ℤ²`.

## Main results

* `StatMech.Universality.half_crossingProb_of_selfDual_dichotomy`: self-dual events have
  probability `1/2` under `ℙ_{1/2}`.
* `StatMech.Universality.percolationProbability_toReal`,
  `StatMech.Universality.percolationProbability_eq_zero_iff_theta`: agreement with
  `StatMech.Percolation.theta`.
* `StatMech.Universality.half_le_criticalProbability_of_subcritical`: `θ(1/2) = 0 → 1/2 ≤ p_c`.
* `StatMech.Universality.criticalProbability_le_half_of_sharpThreshold`.
* `StatMech.Universality.kesten_pc_eq_half_of_bxp`,
  `StatMech.Universality.kesten_no_percolation_at_pc`:
  conditional Kesten theorem.

## References

* H. Kesten, *The critical probability of bond percolation on the square lattice equals 1/2*,
  Comm. Math. Phys. 74 (1980), 41–59.
* T. E. Harris, *A lower bound for the critical probability in a certain percolation process*,
  Proc. Cambridge Philos. Soc. 56 (1960), 13–20.
* G. R. Grimmett, *Percolation*, 2nd ed., Springer, 1999, §11.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace StatMech

namespace Universality

open StatMech.Lattice StatMech.TwoDim

/-- The Bernoulli bond percolation measure `ℙ_{1/2}` on configurations of `ℤ²`. -/
noncomputable def halfMeasure : Measure (ConfigSpace (Sym2 (Site 2))) :=
  bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one

/-- `ℙ_{1/2}` is a probability measure. -/
instance instIsProbabilityMeasure_halfMeasure : IsProbabilityMeasure halfMeasure := by
  unfold halfMeasure; infer_instance

/-- Unfolding lemma for `halfMeasure`. -/
theorem halfMeasure_eq :
    halfMeasure = bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one := rfl

/-- `dualConfig` is measurable. -/
theorem measurable_dualConfig :
    Measurable (dualConfig : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))) := by
  rw [dualConfig_eq_comp]
  exact measurable_complement.comp measurable_reindex

/-- Self-duality at `p = 1/2`: `dualConfig` preserves `ℙ_{1/2}`. -/
theorem dualConfig_preserves_half :
    Measure.map dualConfig halfMeasure = halfMeasure :=
  bernoulliProductMeasure_selfDual_half

/-- If `R` preserves `ℙ_{1/2}`, so does `R ∘ dualConfig`. -/
theorem selfDualRotation_preserves_half
    (R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2)))
    (hRmeas : Measurable R) (hRpres : Measure.map R halfMeasure = halfMeasure) :
    Measure.map (R ∘ dualConfig) halfMeasure = halfMeasure := by
  rw [← Measure.map_map hRmeas measurable_dualConfig, dualConfig_preserves_half, hRpres]

/-- An event `H` whose complement is its preimage under `R ∘ dualConfig`, with `R` preserving
`ℙ_{1/2}`, has `ℙ_{1/2}(H) = 1/2`. In the literature `H` is the left–right crossing of an
`(n + 1) × n` rectangle; here the identity `Hᶜ = (R ∘ dualConfig)⁻¹ H` is a hypothesis. -/
theorem half_crossingProb_of_selfDual_dichotomy
    {H : Set (ConfigSpace (Sym2 (Site 2)))} (hHm : MeasurableSet H)
    {R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))}
    (hRmeas : Measurable R) (hRpres : Measure.map R halfMeasure = halfMeasure)
    (hdich : Hᶜ = (R ∘ dualConfig) ⁻¹' H) :
    halfMeasure.real H = 1 / 2 := by
  have hSmeas : Measurable (R ∘ dualConfig) := hRmeas.comp measurable_dualConfig
  have hSpres : Measure.map (R ∘ dualConfig) halfMeasure = halfMeasure :=
    selfDualRotation_preserves_half R hRmeas hRpres
  have hpre : halfMeasure.real ((R ∘ dualConfig) ⁻¹' H) = halfMeasure.real H := by
    have h1 : halfMeasure ((R ∘ dualConfig) ⁻¹' H) = halfMeasure H := by
      rw [← Measure.map_apply hSmeas hHm, hSpres]
    unfold Measure.real; rw [h1]
  rw [← hdich, measureReal_compl hHm, probReal_univ] at hpre
  linarith

/-- `percolationProbability` is `StatMech.Percolation.theta` as an extended real. -/
theorem percolationProbability_toReal (d : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    (percolationProbability d p hp).toReal = Percolation.theta d p hp := rfl

/-- `θ(p) = 0` in either formulation. -/
theorem percolationProbability_eq_zero_iff_theta (d : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    percolationProbability d p hp = 0 ↔ Percolation.theta d p hp = 0 := by
  rw [← percolationProbability_toReal, ENNReal.toReal_eq_zero_iff]
  exact ⟨Or.inl, fun h => h.resolve_right (measure_ne_top _ _)⟩

/-- `θ(p)` does not depend on the proof of `p ≤ 1`. -/
theorem percolationProbability_congr {d : ℕ} {p q : ℝ≥0}
    (hp : p ≤ 1) (hq : q ≤ 1) (h : p = q) :
    percolationProbability d p hp = percolationProbability d q hq := by
  subst h; rfl

/-- The set of subcritical densities is bounded above by `1`. -/
theorem subcriticalDensities_bddAbove (d : ℕ) : BddAbove (subcriticalDensities d) :=
  ⟨1, by rintro p ⟨_, hp1, _⟩; exact hp1⟩

/-- If `θ(1/2) = 0` then `1/2` is a subcritical density. -/
theorem half_mem_subcriticalDensities
    (h : percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0) :
    ((1 : ℝ) / 2) ∈ subcriticalDensities 2 := by
  have hp0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hp1 : (1 : ℝ) / 2 ≤ 1 := by norm_num
  refine ⟨hp0, hp1, ?_⟩
  rw [percolationProbability_congr (by exact_mod_cast hp1) half_le_one
    (show (⟨(1 : ℝ) / 2, hp0⟩ : ℝ≥0) = (2⁻¹ : ℝ≥0) by
      apply NNReal.coe_injective
      change (1 : ℝ) / 2 = ((2⁻¹ : ℝ≥0) : ℝ)
      rw [NNReal.coe_inv]; norm_num)]
  exact h

/-- If `θ(1/2) = 0` then `1/2 ≤ p_c`. -/
theorem half_le_criticalProbability_of_subcritical
    (h : percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0) :
    (1 : ℝ) / 2 ≤ criticalProbability 2 := by
  unfold criticalProbability
  exact le_csSup (subcriticalDensities_bddAbove 2) (half_mem_subcriticalDensities h)

/-- If the probabilities of `boxFam n` tend to `0` for every `p < p_c` but equal `1/2` at `p = 1/2`,
then `p_c ≤ 1/2`. -/
theorem criticalProbability_le_half_of_sharpThreshold
    {boxFam : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
    (hSharpThreshold : ∀ (p : ℝ≥0) (hp : p ≤ 1), (p : ℝ) < criticalProbability 2 →
        Tendsto (fun n => (bernoulliProductMeasure p hp).real (boxFam n)) atTop (𝓝 0))
    (hbalance : ∀ n : ℕ, halfMeasure.real (boxFam n) = 1 / 2) :
    criticalProbability 2 ≤ (1 : ℝ) / 2 := by
  by_contra hgt
  rw [not_le] at hgt
  have hlt : ((2⁻¹ : ℝ≥0) : ℝ) < criticalProbability 2 := by
    have hc : ((2⁻¹ : ℝ≥0) : ℝ) = 1 / 2 := by rw [NNReal.coe_inv]; norm_num
    rw [hc]; exact hgt
  have hT := hSharpThreshold (2⁻¹ : ℝ≥0) half_le_one hlt
  have hconst : (fun n => (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one).real (boxFam n))
      = fun _ => (1 : ℝ) / 2 := funext hbalance
  rw [hconst] at hT
  have hcontra := tendsto_nhds_unique hT tendsto_const_nhds
  norm_num at hcontra

/-- **Kesten theorem** `p_c(ℤ²) = 1/2` for bond percolation (Kesten, "The critical probability of
bond percolation on the square lattice equals 1/2", 1980), in a conditional form.

The hypotheses that carry the mathematical content of Kesten's theorem are assumed:
* `hCorLowerBound` (with `hbxp`): `θ(1/2) = 0`. This is Harris's theorem; in the literature it
  follows from RSW (open circuits in disjoint annuli) and gives `1/2 ≤ p_c`.
* `hSharpThreshold`: for every `p < p_c`, `ℙ_p(boxFam n) → 0`. This is the subcritical decay of
  crossing probabilities (Kesten's sharp-threshold argument, or Menshikov / Aizenman–Barsky
  exponential decay); it gives `p_c ≤ 1/2`.
* `hdich`, `hRpres`, `hHm`: `boxFam` is an exactly self-dual family, i.e. its complement is its
  preimage under a `ℙ_{1/2}`-preserving map `R ∘ dualConfig`. In the literature this is planar
  duality for the left–right crossing of an `(n + 1) × n` rectangle; no family satisfying `hdich`
  is constructed in Atlas.
What is proved is the self-duality computation `ℙ_{1/2}(boxFam n) = 1/2` and the order argument.

`hbxp` enters only through `hCorLowerBound`.

See also `StatMech.TwoDim.kesten_pc_eq_half`, a conditional form stated with an abstract crossing
function. -/
theorem kesten_pc_eq_half_of_bxp
    {ρ : ℝ} {R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))}
    {boxFam : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
    (hbxp : BoxCrossingProperty halfMeasure ρ)
    (hCorLowerBound : BoxCrossingProperty halfMeasure ρ →
        percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0)
    (hHm : ∀ n, MeasurableSet (boxFam n))
    (hRmeas : Measurable R) (hRpres : Measure.map R halfMeasure = halfMeasure)
    (hdich : ∀ n, (boxFam n)ᶜ = (R ∘ dualConfig) ⁻¹' (boxFam n))
    (hSharpThreshold : ∀ (p : ℝ≥0) (hp : p ≤ 1), (p : ℝ) < criticalProbability 2 →
        Tendsto (fun n => (bernoulliProductMeasure p hp).real (boxFam n)) atTop (𝓝 0)) :
    criticalProbability 2 = 1 / 2 := by
  have hbalance : ∀ n : ℕ, halfMeasure.real (boxFam n) = 1 / 2 := fun n =>
    half_crossingProb_of_selfDual_dichotomy (hHm n) hRmeas hRpres (hdich n)
  have hge : (1 : ℝ) / 2 ≤ criticalProbability 2 :=
    half_le_criticalProbability_of_subcritical (hCorLowerBound hbxp)
  have hle : criticalProbability 2 ≤ (1 : ℝ) / 2 :=
    criticalProbability_le_half_of_sharpThreshold hSharpThreshold hbalance
  linarith

/-- Conditional Kesten theorem together with `θ(p_c) = 0`: under the hypotheses of
`kesten_pc_eq_half_of_bxp`, `p_c = 1/2` and `θ(1/2) = 0`. The second conjunct is
`hCorLowerBound hbxp`, i.e. it is assumed (Harris 1960), not derived. -/
theorem kesten_no_percolation_at_pc
    {ρ : ℝ} {R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))}
    {boxFam : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
    (hbxp : BoxCrossingProperty halfMeasure ρ)
    (hCorLowerBound : BoxCrossingProperty halfMeasure ρ →
        percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0)
    (hHm : ∀ n, MeasurableSet (boxFam n))
    (hRmeas : Measurable R) (hRpres : Measure.map R halfMeasure = halfMeasure)
    (hdich : ∀ n, (boxFam n)ᶜ = (R ∘ dualConfig) ⁻¹' (boxFam n))
    (hSharpThreshold : ∀ (p : ℝ≥0) (hp : p ≤ 1), (p : ℝ) < criticalProbability 2 →
        Tendsto (fun n => (bernoulliProductMeasure p hp).real (boxFam n)) atTop (𝓝 0)) :
    criticalProbability 2 = 1 / 2 ∧
      percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0 :=
  ⟨kesten_pc_eq_half_of_bxp hbxp hCorLowerBound hHm hRmeas hRpres hdich hSharpThreshold,
    hCorLowerBound hbxp⟩

end Universality

end StatMech

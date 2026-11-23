/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Alignment.ScoreSignificance.GumbelTail
public import MathlibExt.Probability.Renewal.ScoreLadder
public import MathlibExt.Probability.Renewal.LatticeConstants
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Renewal theorem for ladder heights: the tail hypotheses of the Gumbel limit

`GumbelTail` proves the Gumbel limit (nonlattice) and the liminf/limsup bounds (lattice) for the
maximal segment score of Cramér scores from `NonlatticeRenewalInput` / `LatticeRenewalInput`,
whose tail fields assume the excursion-height asymptotics

* nonlattice: `(1 - F t) e^{θ t} → C`, i.e. `P(Y > t) ~ C e^{-θ t}`;
* lattice (span `h`): `(1 - F (k h)) e^{θ (k + 1) h} → C`.

This file derives those tail fields from the ladder structure of the score walk and the renewal
theorem, and builds the two inputs (`NonlatticeRenewalInput.ofLadder`,
`LatticeRenewalInput.ofLadder`).

## The derivation

1. *All-time maximum* (Cramér–Lundberg). Cutting the all-time maximum `M'` of the walk at its first
   strict ascending ladder epoch gives a defective renewal equation with the ladder-height law `G`
   (or `g` on the lattice). At the Cramér root, `∫ e^{θ y} dG = 1`, exponential tilting makes it
   proper, and the renewal theorem gives `P(M' > t) ~ C_∞ e^{-θ t}`. This step is the canonical
   `tendsto_scaled_cramerLundberg` (nonlattice, key renewal theorem as hypothesis) and
   `tendsto_exp_mul_maxTail` (lattice, discrete key renewal theorem *proved*) from
   `MathlibExt.Probability.Renewal`.
2. *Excursion height* (Iglehart 1972; proved here, `tendsto_exp_mul_real_lt_of_fixedPoint`). At
   the first descending ladder epoch, with `Y` the excursion height, `D ≤ 0` the walk value and
   `M'` the maximum afterwards, the all-time maximum is `max Y (D + M')` with `M'` independent of
   `(Y, D)`. Splitting `{max Y (D + M') > t}` and applying dominated convergence gives
   `P(Y > t) ~ C_∞ (1 - E e^{θ D}) e^{-θ t}`.

## What is derived and what is assumed

Derived (proved here): the tail fields `NonlatticeRenewalInput.tendsto_tail` (constant
`LadderRenewalData.tailConst`) and `LatticeRenewalInput.tendsto_tail` (constant
`LatticeLadderRenewalData.tailConst`), via `LadderRenewalData.tendsto_tail` and
`LatticeLadderRenewalData.tendsto_tail`; hence the Gumbel limit and the lattice bounds for any
data satisfying the hypotheses below (`NonlatticeRenewalInput.tendsto_gumbel_ofLadder`,
`LatticeRenewalInput.eventually_bounds_ofLadder`).

Assumed (explicit hypotheses):

* *Renewal theorem, nonlattice case only*: `hKRT`, the key renewal theorem for the tilted
  ladder-height law over all `KeyRenewalAdmissible` pairs, exactly as in
  `tendsto_scaled_cramerLundberg`. It holds when the tilted law is nonlattice (Feller XI.1) and is
  not proved. The lattice case assumes no renewal theorem.
* *Ladder-epoch facts* (the strong Markov property at ladder epochs, not imported here):
  the `LadderInput` itself; `LadderFixedPoint` (independence of `M'` from `(Y, D)` and the
  distributional identity `max Y (D + M') =ᵈ M'`); the ascending-ladder renewal equation of `M'`;
  the ladder Cramér identity (Wald's identity at the ascending ladder epoch; not derived from
  `CramerScores.mgf_eq_one`); finiteness of the tilted ladder mean; and in the lattice case,
  aperiodicity of the ladder support and the lattice property of `D` and of the excursion heights
  (`lattice_Y`).
* The fields `cramer`, `nonlattice` / `lattice` of the inputs are passed through: the derivation
  of the ladder data from `CramerScores` is not done here.

## Main results

* `tendsto_exp_mul_real_lt_of_fixedPoint`: excursion-height tail from the all-time-maximum tail.
* `LadderRenewalData.tendsto_tail`, `LatticeLadderRenewalData.tendsto_tail`: the derived tails.
* `NonlatticeRenewalInput.ofLadder`, `LatticeRenewalInput.ofLadder`: the derived inputs, and
  `NonlatticeRenewalInput.tendsto_gumbel_ofLadder`,
  `LatticeRenewalInput.eventually_bounds_ofLadder`.

## Reuse

Renewal theory comes from `MathlibExt.Probability.Renewal.ScoreLadder` (`IsRenewalSolution`,
`ladderTail`, `tendsto_exp_mul_maxTail`) and `MathlibExt.Probability.Renewal.LatticeConstants`
(`KeyRenewalAdmissible`, `tendsto_scaled_cramerLundberg`); the targets are `GumbelTail`'s
structures. No renewal, ladder or Cramér–Lundberg concept is redefined. Independence is Mathlib's
`IndepFun` through `indepFun_iff_map_prod_eq_prod_map_map`, and the limit is
`tendsto_integral_filter_of_dominated_convergence`.

## References

* D. L. Iglehart, *Extreme values in the GI/G/1 queue*, Ann. Math. Statist. 43 (1972),
  627–635.
* S. Karlin and A. Dembo, *Limit distributions of maximal segmental score among Markov-dependent
  partial sums*, Adv. Appl. Probab. 24 (1992), 113–140.
* W. Feller, *An Introduction to Probability Theory and Its Applications*, Vol. II, 2nd ed.,
  Wiley, 1971, §§XI.1, XI.6, XII.
-/

@[expose] public section

namespace Cslib.Bioinformatics.Alignment.ScoreSignificance

open MeasureTheory ProbabilityTheory Filter Topology
open MathlibExt.Probability.Renewal MathlibExt.Probability.Renewal.LatticeConstants

/-! ### From the all-time maximum to the excursion height -/

section Excursion

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Y D M' : Ω → ℝ}

private theorem antitone_real_lt (P : Measure Ω) [IsFiniteMeasure P] (M' : Ω → ℝ) :
    Antitone fun u => P.real {ω | u < M' ω} := fun _ _ huv =>
  measureReal_mono fun _ (h : _ < _) => lt_of_le_of_lt huv h

private theorem real_le_lt_add_eq_integral [IsProbabilityMeasure P] (hY : Measurable Y)
    (hD : Measurable D) (hM : Measurable M') (hind : IndepFun (fun ω => (Y ω, D ω)) M' P)
    (t : ℝ) :
    P.real {ω | Y ω ≤ t ∧ t < D ω + M' ω} =
      ∫ ω, {ω | Y ω ≤ t}.indicator (fun ω => P.real {ω' | t - D ω < M' ω'}) ω ∂P := by
  set V : Ω → ℝ × ℝ := fun ω => (Y ω, D ω) with hV
  have hVm : Measurable V := hY.prodMk hD
  set S : Set ((ℝ × ℝ) × ℝ) := {q | q.1.1 ≤ t ∧ t < q.1.2 + q.2} with hS
  have hSm : MeasurableSet S :=
    (measurableSet_le (measurable_fst.comp measurable_fst) measurable_const).inter
      (measurableSet_lt measurable_const
        ((measurable_snd.comp measurable_fst).add measurable_snd))
  have hset : {ω | Y ω ≤ t ∧ t < D ω + M' ω} = (fun ω => (V ω, M' ω)) ⁻¹' S := rfl
  have hfib : ∀ v : ℝ × ℝ, Prod.mk v ⁻¹' S = if v.1 ≤ t then Set.Ioi (t - v.2) else ∅ := by
    intro v; ext m
    by_cases hv : v.1 ≤ t
    · rw [ite_eq_left hv, Set.mem_Ioi]
      change (v.1 ≤ t ∧ t < v.2 + m) ↔ _
      exact ⟨fun h => by linarith [h.2], fun h => ⟨hv, by linarith⟩⟩
    · rw [ite_eq_right hv]
      change (v.1 ≤ t ∧ t < v.2 + m) ↔ m ∈ (∅ : Set ℝ)
      simp [hv]
  have hZm : Measurable fun ω => P.real {ω' | t - D ω < M' ω'} :=
    (antitone_real_lt P M').measurable.comp (measurable_const.sub hD)
  have hlin : P {ω | Y ω ≤ t ∧ t < D ω + M' ω} =
      ∫⁻ ω, ENNReal.ofReal ({ω | Y ω ≤ t}.indicator
        (fun ω => P.real {ω' | t - D ω < M' ω'}) ω) ∂P := by
    rw [hset, ← Measure.map_apply (hVm.prodMk hM) hSm,
      (indepFun_iff_map_prod_eq_prod_map_map hVm.aemeasurable hM.aemeasurable).1 hind,
      Measure.prod_apply hSm, lintegral_map (measurable_measure_prodMk_left hSm) hVm]
    refine lintegral_congr fun ω => ?_
    rw [hfib]
    by_cases hy : Y ω ≤ t
    · simp only [hV, hy, ↓reduceIte, Set.indicator_of_mem (show ω ∈ {ω | Y ω ≤ t} from hy)]
      rw [Measure.map_apply hM measurableSet_Ioi, ofReal_measureReal]; rfl
    · simp [hV, hy]
  rw [measureReal_def, hlin, integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun ω => Set.indicator_nonneg (fun _ _ => measureReal_nonneg) ω)
    (hZm.indicator (measurableSet_le hY measurable_const)).aestronglyMeasurable]

/-- **Excursion-height tail from the all-time-maximum tail.** Let `Y` be the height of the first
ladder excursion (the maximum of the walk before its first descending ladder epoch), `D ≤ 0` the
walk at that epoch, and `M'` the all-time maximum of the walk after it. The strong Markov property
at the descending ladder epoch says that `M'` is independent of `(Y, D)` (`hind`) and that
`max Y (D + M')`, the all-time maximum, has the law of `M'` (`hfix`). If the tail of `M'` satisfies
`e^{θ u} P(M' > u) → C` along the points `s i` (`hZ`, and its shifted form `hz`) and is bounded
by `B` (`hB`), then
`e^{θ s} P(Y > s) → C (1 - E e^{θ D})` along the same points (Iglehart 1972). -/
theorem tendsto_exp_mul_real_lt_of_fixedPoint [IsProbabilityMeasure P] {θ : ℝ} (hθ : 0 < θ)
    (hY : Measurable Y) (hD : Measurable D) (hM : Measurable M') (hD0 : ∀ᵐ ω ∂P, D ω ≤ 0)
    (hind : IndepFun (fun ω => (Y ω, D ω)) M' P)
    (hfix : ∀ t, P.real {ω | t < max (Y ω) (D ω + M' ω)} = P.real {ω | t < M' ω})
    {ι : Type*} {L : Filter ι} [L.IsCountablyGenerated] {s : ι → ℝ} (hs : Tendsto s L atTop)
    {B C : ℝ} (hB : ∀ u, 0 ≤ u → Real.exp (θ * u) * P.real {ω | u < M' ω} ≤ B)
    (hZ : Tendsto (fun i => Real.exp (θ * s i) * P.real {ω | s i < M' ω}) L (𝓝 C))
    (hz : ∀ᵐ ω ∂P, Tendsto (fun i => Real.exp (θ * (s i - D ω)) *
      P.real {ω' | s i - D ω < M' ω'}) L (𝓝 C)) :
    Tendsto (fun i => Real.exp (θ * s i) * P.real {ω | s i < Y ω}) L
      (𝓝 (C * (1 - ∫ ω, Real.exp (θ * D ω) ∂P))) := by
  set Zt : ℝ → ℝ := fun u => P.real {ω | u < M' ω} with hZt
  have hZtm : Measurable Zt := (antitone_real_lt P M').measurable
  set F : ℝ → Ω → ℝ := fun t => {ω | Y ω ≤ t}.indicator
    (fun ω => Real.exp (θ * D ω) * (Real.exp (θ * (t - D ω)) * Zt (t - D ω))) with hF
  have hFm : ∀ t, Measurable (F t) := fun t =>
    ((by fun_prop : Measurable fun x : ℝ => Real.exp (θ * x)).comp hD |>.mul
      (((by fun_prop : Measurable fun x : ℝ => Real.exp (θ * x)).comp
        (measurable_const.sub hD)).mul (hZtm.comp (measurable_const.sub hD)))).indicator
      (measurableSet_le hY measurable_const)
  -- the disjoint decomposition of `{t < max Y (D + M')}`
  have hsplit : ∀ t, Real.exp (θ * t) * P.real {ω | t < Y ω} =
      Real.exp (θ * t) * Zt t - ∫ ω, F t ω ∂P := by
    intro t
    have hU : {ω | t < max (Y ω) (D ω + M' ω)} =
        {ω | t < Y ω} ∪ {ω | Y ω ≤ t ∧ t < D ω + M' ω} := by
      ext ω
      simp only [Set.mem_union, lt_max_iff]
      change (t < Y ω ∨ t < D ω + M' ω) ↔ (t < Y ω ∨ (Y ω ≤ t ∧ t < D ω + M' ω))
      by_cases hy : t < Y ω
      · simp [hy]
      · simp [hy, not_lt.1 hy]
    have hdisj : Disjoint {ω | t < Y ω} {ω | Y ω ≤ t ∧ t < D ω + M' ω} :=
      Set.disjoint_left.2 fun ω (h1 : t < Y ω) (h2 : Y ω ≤ t ∧ _) => by linarith [h2.1]
    have hm2 : MeasurableSet {ω | Y ω ≤ t ∧ t < D ω + M' ω} :=
      (measurableSet_le hY measurable_const).inter (measurableSet_lt measurable_const (hD.add hM))
    have hZt : Zt t = P.real {ω | t < Y ω} + P.real {ω | Y ω ≤ t ∧ t < D ω + M' ω} := by
      change P.real {ω | t < M' ω} = _
      rw [← hfix t, hU, measureReal_union hdisj hm2]
    have hI : Real.exp (θ * t) * P.real {ω | Y ω ≤ t ∧ t < D ω + M' ω} = ∫ ω, F t ω ∂P := by
      rw [real_le_lt_add_eq_integral hY hD hM hind t, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      by_cases hy : Y ω ≤ t
      · have hmem : ω ∈ {ω | Y ω ≤ t} := hy
        simp only [hF, Set.indicator_of_mem hmem]
        rw [← mul_assoc, ← Real.exp_add]; ring_nf; rfl
      · have hmem : ω ∉ {ω | Y ω ≤ t} := hy
        simp only [hF, Set.indicator_of_notMem hmem, mul_zero]
    rw [← hI, hZt]; ring
  have hB0 : 0 ≤ B := le_trans (mul_nonneg (Real.exp_pos _).le measureReal_nonneg) (hB 0 le_rfl)
  have hDCT : Tendsto (fun i => ∫ ω, F (s i) ω ∂P) L
      (𝓝 (∫ ω, Real.exp (θ * D ω) * C ∂P)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => B)
      (Eventually.of_forall fun i => (hFm (s i)).aestronglyMeasurable) ?_ (integrable_const B) ?_
    · filter_upwards [hs.eventually_ge_atTop 0] with i hi
      filter_upwards [hD0] with ω hω
      by_cases hy : Y ω ≤ s i
      · have hmem : ω ∈ {ω | Y ω ≤ s i} := hy
        simp only [hF, Set.indicator_of_mem hmem]
        have h1 : 0 ≤ Real.exp (θ * (s i - D ω)) * Zt (s i - D ω) :=
          mul_nonneg (Real.exp_pos _).le measureReal_nonneg
        have h2 := hB (s i - D ω) (by linarith)
        have h3 : Real.exp (θ * D ω) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le h1)]
        calc Real.exp (θ * D ω) * (Real.exp (θ * (s i - D ω)) * Zt (s i - D ω))
            ≤ 1 * B := mul_le_mul h3 h2 h1 zero_le_one
          _ = B := one_mul B
      · have hmem : ω ∉ {ω | Y ω ≤ s i} := hy
        simp only [hF, Set.indicator_of_notMem hmem, norm_zero]
        exact hB0
    · filter_upwards [hz] with ω hω
      refine (hω.const_mul (Real.exp (θ * D ω))).congr' ?_
      filter_upwards [hs.eventually_ge_atTop (Y ω)] with i hi
      have hmem : ω ∈ {ω | Y ω ≤ s i} := hi
      simp only [hF, Set.indicator_of_mem hmem]
      rfl
  rw [integral_mul_const] at hDCT
  have h := hZ.sub hDCT
  rw [show C - (∫ ω, Real.exp (θ * D ω) ∂P) * C = C * (1 - ∫ ω, Real.exp (θ * D ω) ∂P) by ring]
    at h
  exact h.congr fun i => (hsplit (s i)).symm

end Excursion

/-! ### Ladder data supplied by the strong Markov property (hypotheses) -/

section Assembly

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Descending-ladder fixed point** for an excursion height `Y`: the random variables and
distributional identities that the strong Markov property at the first descending ladder epoch
`T` of the score walk `S` provides (ladder-epoch results), taken as hypotheses. `D = S_T ≤ 0`
is the walk at `T`, `M' = sup_{k ≥ T} (S_k - S_T) ≥ 0` the all-time maximum of the walk after `T`
(independent of `(Y, D)`), and the all-time maximum `max Y (D + M')` of the whole walk has the law
of `M'`. -/
structure LadderFixedPoint (P : Measure Ω) (Y : Ω → ℝ) where
  /-- The walk at the first descending ladder epoch. -/
  D : Ω → ℝ
  /-- The all-time maximum of the walk after the first descending ladder epoch. -/
  M' : Ω → ℝ
  /-- `D` is measurable. -/
  measurable_D : Measurable D
  /-- `M'` is measurable. -/
  measurable_M' : Measurable M'
  /-- `D ≤ 0`. -/
  D_nonpos : ∀ᵐ ω ∂P, D ω ≤ 0
  /-- `M' ≥ 0` (the empty segment). -/
  M'_nonneg : ∀ᵐ ω ∂P, 0 ≤ M' ω
  /-- Strong Markov property: the post-epoch maximum is independent of `(Y, D)`. -/
  indep : IndepFun (fun ω => (Y ω, D ω)) M' P
  /-- Strong Markov property: the all-time maximum `max Y (D + M')` has the law of `M'`. -/
  fixedPoint : ∀ t, P.real {ω | t < max (Y ω) (D ω + M' ω)} = P.real {ω | t < M' ω}

namespace LadderFixedPoint

variable {Y : Ω → ℝ}

private theorem real_lt_of_neg [IsProbabilityMeasure P] (F : LadderFixedPoint P Y) {u : ℝ}
    (hu : u < 0) : P.real {ω | u < F.M' ω} = 1 := by
  rw [← probReal_univ (μ := P)]
  refine measureReal_congr ?_
  filter_upwards [F.M'_nonneg] with ω hω
  change (u < F.M' ω) = True
  simp only [eq_iff_iff, iff_true]; linarith

end LadderFixedPoint

/-- **Ladder renewal data, nonlattice case**, for an excursion height `Y` and Cramér root `θ`: the
descending-ladder fixed point together with the ascending-ladder renewal structure of `M'`
(again from the strong Markov property), taken as hypotheses. `G` is the defective law of
the first strict ascending ladder height (a finite measure on `[0, ∞)`); cutting `M'` at the
first ascending ladder epoch gives `P(M' > t) = ∫ P(M' > t - y) dG(y)` for `t ≥ 0`; the Cramér
root satisfies the ladder identity `∫ e^{θ y} dG(y) = 1` (Wald's identity for the martingale
`e^{θ S_n}` at the ascending ladder epoch); and the tilted ladder mean `∫ y e^{θ y} dG(y)` is
finite. -/
structure LadderRenewalData (P : Measure Ω) (Y : Ω → ℝ) (θ : ℝ) extends LadderFixedPoint P Y where
  /-- The defective law of the first strict ascending ladder height. -/
  G : Measure ℝ
  /-- `G` is finite (its mass is the probability that the walk ever becomes positive). -/
  isFiniteMeasure_G : IsFiniteMeasure G
  /-- Ladder heights are nonnegative. -/
  G_nonneg : ∀ᵐ y ∂G, 0 ≤ y
  /-- The ladder Cramér identity `∫ e^{θ y} dG(y) = 1`. -/
  cramer_ladder : ∫ y, Real.exp (θ * y) ∂G = 1
  /-- The tilted ladder mean `∫ y e^{θ y} dG(y)` is finite. -/
  integrable_mean : Integrable (fun y => y * Real.exp (θ * y)) G
  /-- The defective renewal equation of the all-time maximum. -/
  renewal : ∀ t, 0 ≤ t → P.real {ω | t < M' ω} = ∫ y, P.real {ω | t - y < M' ω} ∂G

/-- The Cramér–Lundberg constant `C_∞ = (1 - G(ℝ)) / (θ ∫ y e^{θ y} dG(y))` of the all-time
maximum, `P(M' > t) ~ C_∞ e^{-θ t}`. -/
noncomputable def LadderRenewalData.allTimeConst {Y : Ω → ℝ} {θ : ℝ}
    (R : LadderRenewalData P Y θ) : ℝ :=
  (1 - R.G.real Set.univ) / (θ * ∫ y, y * Real.exp (θ * y) ∂R.G)

/-- The excursion-height renewal constant `C = C_∞ (1 - E e^{θ D})` (Iglehart 1972). -/
noncomputable def LadderRenewalData.tailConst {Y : Ω → ℝ} {θ : ℝ}
    (R : LadderRenewalData P Y θ) : ℝ :=
  R.allTimeConst * (1 - ∫ ω, Real.exp (θ * R.D ω) ∂P)

/-- A function with a finite limit at `+∞` that is bounded on bounded intervals is bounded on
`[0, ∞)`. -/
private theorem exists_bound_of_tendsto {f : ℝ → ℝ} {C : ℝ} (hf : Tendsto f atTop (𝓝 C))
    (hloc : ∀ T, ∃ B, ∀ t ∈ Set.Icc 0 T, f t ≤ B) : ∃ B, ∀ t, 0 ≤ t → f t ≤ B := by
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hf.eventually (gt_mem_nhds (lt_add_one C)))
  obtain ⟨B, hB⟩ := hloc T
  refine ⟨max B (C + 1), fun t ht => ?_⟩
  by_cases htT : t ≤ T
  · exact (hB t ⟨ht, htT⟩).trans (le_max_left _ _)
  · exact (hT t (not_le.1 htT).le).le.trans (le_max_right _ _)

/-- **Nonlattice excursion tail, derived.** For a measurable excursion height `Y` with nonlattice
ladder renewal data `R`, the key renewal theorem for the tilted ladder-height law `G^θ`
(`hKRT`, in the form of `tendsto_scaled_cramerLundberg`) gives
`P(Y > t) e^{θ t} → C`, `C = C_∞ (1 - E e^{θ D})`. This is the tail hypothesis
`NonlatticeRenewalInput.tendsto_tail` of the Gumbel limit. -/
theorem LadderRenewalData.tendsto_tail [IsProbabilityMeasure P] {Y : Ω → ℝ} {θ : ℝ}
    (hY : Measurable Y) (hθ : 0 < θ) (R : LadderRenewalData P Y θ)
    (hKRT : ∀ V v : ℝ → ℝ, KeyRenewalAdmissible V v →
      (∀ t, V t = v t + ∫ x, V (t - x) ∂(R.G.tilted (fun x => θ * x))) →
      Tendsto V atTop (𝓝 ((∫ s in Set.Ioi 0, v s) / ∫ x, x ∂(R.G.tilted (fun x => θ * x))))) :
    Tendsto (fun t => P.real {ω | t < Y ω} * Real.exp (θ * t)) atTop (𝓝 R.tailConst) := by
  have := R.isFiniteMeasure_G
  set Zt : ℝ → ℝ := fun u => P.real {ω | u < R.M' ω} with hZt
  set Zf : ℝ → ℝ := (Set.Ici 0).indicator Zt with hZf
  have hZtm : Measurable Zt := (antitone_real_lt P R.M').measurable
  have hZfm : Measurable Zf := hZtm.indicator measurableSet_Ici
  have hZfneg : ∀ t < 0, Zf t = 0 := fun t ht =>
    Set.indicator_of_notMem (fun h => absurd (Set.mem_Ici.1 h) (not_le.2 ht)) _
  have hZfb : ∀ t, |Zf t| ≤ 1 := fun t => by
    rw [abs_of_nonneg (Set.indicator_nonneg (fun _ _ => measureReal_nonneg) t)]
    by_cases ht : t ∈ Set.Ici (0 : ℝ)
    · rw [Set.indicator_of_mem ht]; exact measureReal_le_one
    · rw [Set.indicator_of_notMem ht]; exact zero_le_one
  have hren : ∀ t, Zf t = (Set.Ici 0).indicator (fun s => R.G.real (Set.Ioi s)) t +
      ∫ y, Zf (t - y) ∂R.G := by
    intro t
    by_cases ht : 0 ≤ t
    · rw [hZf, Set.indicator_of_mem (Set.mem_Ici.2 ht), Set.indicator_of_mem (Set.mem_Ici.2 ht)]
      change P.real {ω | t < R.M' ω} = _
      have hpt : ∀ y, Zt (t - y) =
          (Set.Ioi t).indicator (fun _ => (1 : ℝ)) y + Zf (t - y) := by
        intro y
        by_cases hy : y ≤ t
        · rw [Set.indicator_of_notMem (by simpa using hy), zero_add, hZf,
            Set.indicator_of_mem (Set.mem_Ici.2 (by linarith))]
        · rw [Set.indicator_of_mem (by simpa using hy), hZfneg _ (by linarith), add_zero]
          exact R.real_lt_of_neg (by linarith)
      have hint : Integrable (fun y => Zf (t - y)) R.G :=
        Integrable.of_bound (C := 1)
          (hZfm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
          (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hZfb _)
      rw [R.renewal t ht, integral_congr_ae (Eventually.of_forall hpt),
        integral_add ((integrable_const _).indicator measurableSet_Ioi) hint,
        integral_indicator_const _ measurableSet_Ioi, smul_eq_mul, mul_one]
    · rw [hZfneg t (not_le.1 ht), Set.indicator_of_notMem (fun h => ht (Set.mem_Ici.1 h)),
        zero_add, integral_eq_zero_of_ae]
      filter_upwards [R.G_nonneg] with y hy
      exact hZfneg _ (by linarith [not_le.1 ht])
  have hC0 := tendsto_scaled_cramerLundberg hθ R.cramer_ladder R.G_nonneg R.integrable_mean
    hZfm hZfneg ⟨1, hZfb⟩ hren hKRT
  have hC : Tendsto (fun t => Real.exp (θ * t) * Zt t) atTop (𝓝 R.allTimeConst) := by
    refine hC0.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    rw [hZf, Set.indicator_of_mem (Set.mem_Ici.2 ht)]
  obtain ⟨B, hB⟩ := exists_bound_of_tendsto hC fun T => ⟨Real.exp (θ * T), fun t ht =>
    (mul_le_of_le_one_right (Real.exp_pos _).le measureReal_le_one).trans
      (Real.exp_le_exp.2 (by nlinarith [ht.2]))⟩
  have h := tendsto_exp_mul_real_lt_of_fixedPoint hθ hY R.measurable_D R.measurable_M'
    R.D_nonpos R.indep R.fixedPoint (L := atTop) (s := id) tendsto_id hB hC
    (Eventually.of_forall fun ω => hC.comp (tendsto_atTop_add_const_right _ _ tendsto_id))
  exact h.congr fun t => mul_comm _ _

/-- **Ladder renewal data, lattice case** with span `h`, for an excursion height `Y` and Cramér
root `θ`: the descending-ladder fixed point with `D` on the lattice `-hℕ`, and the lattice
ascending-ladder renewal structure of `M'` (strong Markov property), taken as hypotheses.
`g j` is the defective probability that the first strict ascending ladder height equals `j h`;
cutting `M'` at the first ascending ladder epoch gives the defective renewal equation
`P(M' > k h) = ∑_{j > k} g j + ∑_{j ≤ k} g j P(M' > (k - j) h)` (`IsRenewalSolution`); the
ladder Cramér identity is `∑ g j e^{θ h j} = 1`; the ladder support is aperiodic; and the tilted
ladder mean is finite. These are exactly the inputs of `tendsto_exp_mul_maxTail`, whose
discrete key renewal theorem is proved, so no renewal theorem is assumed in the lattice case. -/
structure LatticeLadderRenewalData (P : Measure Ω) (Y : Ω → ℝ) (θ h : ℝ)
    extends LadderFixedPoint P Y where
  /-- `D` lies on the lattice `-hℕ`. -/
  D_lattice : ∀ᵐ ω ∂P, ∃ n : ℕ, D ω = -(n * h)
  /-- The defective lattice law of the first strict ascending ladder height (in units of `h`). -/
  g : ℕ → ℝ
  /-- Strict ladder heights are positive. -/
  g_zero : g 0 = 0
  /-- `g ≥ 0`. -/
  g_nonneg : ∀ j, 0 ≤ g j
  /-- The ladder Cramér identity `∑ g j e^{θ h j} = 1`. -/
  cramer_ladder : HasSum (fun j : ℕ => g j * Real.exp (θ * h * j)) 1
  /-- The ladder support is aperiodic. -/
  aperiodic : Nat.setGcd {j | 0 < g j} = 1
  /-- The tilted ladder mean `∑ j g j e^{θ h j}`. -/
  tiltedMean : ℝ
  /-- The tilted ladder mean is finite. -/
  hasSum_tiltedMean : HasSum (fun j : ℕ => (j : ℝ) * (g j * Real.exp (θ * h * j))) tiltedMean
  /-- The defective lattice renewal equation of the all-time maximum. -/
  renewal : IsRenewalSolution g (ladderTail g) fun k => P.real {ω | (k : ℝ) * h < M' ω}

/-- The lattice Cramér–Lundberg constant `C_∞ = (1 - ∑ g) / ((e^{θ h} - 1) μ_θ)` of the all-time
maximum, `P(M' > k h) ~ C_∞ e^{-θ h k}`. -/
noncomputable def LatticeLadderRenewalData.allTimeConst {Y : Ω → ℝ} {θ h : ℝ}
    (R : LatticeLadderRenewalData P Y θ h) : ℝ :=
  (1 - ∑' j, R.g j) / ((Real.exp (θ * h) - 1) * R.tiltedMean)

/-- The lattice excursion-height renewal constant `C = e^{θ h} C_∞ (1 - E e^{θ D})`, in the
normalization `P(Y > k h) ~ C e^{-θ (k + 1) h}` of `LatticeRenewalInput`. -/
noncomputable def LatticeLadderRenewalData.tailConst {Y : Ω → ℝ} {θ h : ℝ}
    (R : LatticeLadderRenewalData P Y θ h) : ℝ :=
  Real.exp (θ * h) * (R.allTimeConst * (1 - ∫ ω, Real.exp (θ * R.D ω) ∂P))

/-- **Lattice excursion tail, derived** (no renewal-theorem hypothesis). For a measurable
excursion height `Y` with lattice ladder renewal data `R` (span `h`), the proved discrete key
renewal theorem (`tendsto_exp_mul_maxTail`) gives `P(Y > k h) e^{θ (k + 1) h} → C`,
`C = e^{θ h} C_∞ (1 - E e^{θ D})`. This is the tail hypothesis
`LatticeRenewalInput.tendsto_tail` of the lattice bounds. -/
theorem LatticeLadderRenewalData.tendsto_tail [IsProbabilityMeasure P] {Y : Ω → ℝ} {θ h : ℝ}
    (hY : Measurable Y) (hθ : 0 < θ) (hh : 0 < h) (R : LatticeLadderRenewalData P Y θ h) :
    Tendsto (fun k : ℕ => P.real {ω | (k : ℝ) * h < Y ω} * Real.exp (θ * ((k + 1) * h)))
      atTop (𝓝 R.tailConst) := by
  set Zt : ℝ → ℝ := fun u => P.real {ω | u < R.M' ω} with hZt
  have hC : Tendsto (fun k : ℕ => Real.exp (θ * h * k) * Zt (k * h)) atTop
      (𝓝 R.allTimeConst) :=
    tendsto_exp_mul_maxTail (mul_pos hθ hh) R.g_zero R.g_nonneg R.cramer_ladder R.aperiodic
      R.hasSum_tiltedMean R.renewal
  have hs : Tendsto (fun k : ℕ => (k : ℝ) * h) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hh
  have hC' : Tendsto (fun k : ℕ => Real.exp (θ * ((k : ℝ) * h)) * Zt (k * h)) atTop
      (𝓝 R.allTimeConst) := hC.congr fun k => by ring_nf
  -- a bound on `[0, ∞)` from the bounded lattice sequence
  obtain ⟨B₀, hB₀⟩ := hC.bddAbove_range
  have hB : ∀ u, 0 ≤ u → Real.exp (θ * u) * Zt u ≤ Real.exp (θ * h) * B₀ := by
    intro u hu
    set k := ⌊u / h⌋₊
    have hk1 : (k : ℝ) * h ≤ u := by
      have := Nat.floor_le (div_nonneg hu hh.le); rwa [le_div_iff₀ hh] at this
    have hk2 : u < ((k : ℝ) + 1) * h := by
      have := Nat.lt_floor_add_one (u / h); rwa [div_lt_iff₀ hh] at this
    have hZle : Zt u ≤ Zt (k * h) := antitone_real_lt P R.M' hk1
    have hexp : Real.exp (θ * u) ≤ Real.exp (θ * h) * Real.exp (θ * h * k) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by nlinarith)
    calc Real.exp (θ * u) * Zt u ≤ (Real.exp (θ * h) * Real.exp (θ * h * k)) * Zt (k * h) :=
          mul_le_mul hexp hZle measureReal_nonneg (by positivity)
      _ = Real.exp (θ * h) * (Real.exp (θ * h * k) * Zt (k * h)) := by ring
      _ ≤ Real.exp (θ * h) * B₀ :=
          mul_le_mul_of_nonneg_left (hB₀ ⟨k, rfl⟩) (Real.exp_pos _).le
  have hz : ∀ᵐ ω ∂P, Tendsto (fun k : ℕ => Real.exp (θ * ((k : ℝ) * h - R.D ω)) *
      Zt ((k : ℝ) * h - R.D ω)) atTop (𝓝 R.allTimeConst) := by
    filter_upwards [R.D_lattice] with ω ⟨n, hn⟩
    refine ((tendsto_add_atTop_iff_nat n).2 hC').congr fun k => ?_
    rw [hn]; push_cast; ring_nf
  have hlim := tendsto_exp_mul_real_lt_of_fixedPoint hθ hY R.measurable_D R.measurable_M'
    R.D_nonpos R.indep R.fixedPoint hs hB hC' hz
  refine (hlim.const_mul (Real.exp (θ * h))).congr fun k => ?_
  rw [show θ * ((k + 1) * h) = θ * h + θ * (k * h) by ring, Real.exp_add]; ring

/-- The excursion-height tail: `P(Y 0 > t) = 1 - F t`. -/
theorem LadderInput.real_Y_lt_eq_one_sub [IsProbabilityMeasure P] {M : ℕ → Ω → ℝ}
    (L : LadderInput P M) (t : ℝ) : P.real {ω | t < L.Y 0 ω} = 1 - L.F t := by
  have hset : {ω | t < L.Y 0 ω} = {ω | L.Y 0 ω ≤ t}ᶜ := by ext ω; simp
  rw [hset, measureReal_compl (measurableSet_le (L.measurable_Y 0) measurable_const),
    probReal_univ, L.real_Y_le 0 t]

/-- **Derived nonlattice renewal input.** From Cramér scores `hX` that are nonlattice (`hnl`), the
ladder input `L` (a `LadderInput`, taken as a hypothesis), nonlattice ladder renewal data `R`
for the first excursion height `L.Y 0` (strong-Markov consequences, taken as hypotheses),
and the key renewal theorem for the tilted ladder-height law (`hKRT`, assumed), this builds the
`NonlatticeRenewalInput` of the Gumbel limit with its tail hypothesis `tendsto_tail` *derived*
(renewal constant `C = R.tailConst`). -/
noncomputable def NonlatticeRenewalInput.ofLadder [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    {θ : ℝ} (hX : CramerScores P X θ) (hnl : ∀ h > 0, ¬ ∀ᵐ ω ∂P, ∃ k : ℤ, X 0 ω = k * h)
    (L : LadderInput P (maxSegmentScoreRV X)) (R : LadderRenewalData P (L.Y 0) θ)
    (hKRT : ∀ V v : ℝ → ℝ, KeyRenewalAdmissible V v →
      (∀ t, V t = v t + ∫ x, V (t - x) ∂(R.G.tilted (fun x => θ * x))) →
      Tendsto V atTop (𝓝 ((∫ s in Set.Ioi 0, v s) / ∫ x, x ∂(R.G.tilted (fun x => θ * x))))) :
    NonlatticeRenewalInput P X where
  θ := θ
  cramer := hX
  nonlattice := hnl
  ladder := L
  C := R.tailConst
  tendsto_tail := by
    refine (R.tendsto_tail (L.measurable_Y 0) hX.pos hKRT).congr fun t => ?_
    rw [L.real_Y_lt_eq_one_sub]

/-- **Gumbel limit with derived renewal input**: for nonlattice Cramér scores, given the ladder
input, the ladder renewal data and the key renewal theorem for the tilted ladder-height law,
`P(Mₙ ≤ log n / θ + x) → exp (-K e^{-θ x})` with `K = C / A`, `C = C_∞ (1 - E e^{θ D})`. -/
theorem NonlatticeRenewalInput.tendsto_gumbel_ofLadder [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {θ : ℝ} (hX : CramerScores P X θ)
    (hnl : ∀ h > 0, ¬ ∀ᵐ ω ∂P, ∃ k : ℤ, X 0 ω = k * h)
    (L : LadderInput P (maxSegmentScoreRV X)) (R : LadderRenewalData P (L.Y 0) θ)
    (hKRT : ∀ V v : ℝ → ℝ, KeyRenewalAdmissible V v →
      (∀ t, V t = v t + ∫ x, V (t - x) ∂(R.G.tilted (fun x => θ * x))) →
      Tendsto V atTop (𝓝 ((∫ s in Set.Ioi 0, v s) / ∫ x, x ∂(R.G.tilted (fun x => θ * x)))))
    (x : ℝ) :
    Tendsto (fun n : ℕ => P.real {ω | maxSegmentScoreRV X n ω ≤ Real.log n / θ + x}) atTop
      (𝓝 (Real.exp (-(R.tailConst / L.A * Real.exp (-(θ * x)))))) :=
  (NonlatticeRenewalInput.ofLadder hX hnl L R hKRT).tendsto_gumbel x

/-- **Derived lattice renewal input** (no renewal-theorem hypothesis). From Cramér scores `hX` on
the lattice `hℤ` (`hlat`), the ladder input `L` with excursion heights on `hℤ` (`hlatY`; both
ladder-epoch facts, taken as hypotheses) and lattice ladder renewal data `R` for `L.Y 0` (taken as
hypotheses), this builds the `LatticeRenewalInput` of the lattice bounds with its tail hypothesis
`tendsto_tail` *derived* (renewal constant `C = R.tailConst`). -/
noncomputable def LatticeRenewalInput.ofLadder [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    {θ h : ℝ} (hX : CramerScores P X θ) (hh : 0 < h) (hlat : ∀ i, ∀ᵐ ω ∂P, ∃ k : ℤ, X i ω = k * h)
    (L : LadderInput P (maxSegmentScoreRV X)) (hlatY : ∀ i, ∀ᵐ ω ∂P, ∃ k : ℤ, L.Y i ω = k * h)
    (R : LatticeLadderRenewalData P (L.Y 0) θ h) : LatticeRenewalInput P X where
  θ := θ
  h := h
  cramer := hX
  h_pos := hh
  lattice := hlat
  ladder := L
  lattice_Y := hlatY
  C := R.tailConst
  tendsto_tail := by
    refine (R.tendsto_tail (L.measurable_Y 0) hX.pos hh).congr fun k => ?_
    rw [L.real_Y_lt_eq_one_sub]

/-- **Lattice bounds with derived renewal input**: for lattice Cramér scores, given the ladder
input and the lattice ladder renewal data, for every `ε > 0`, eventually
`exp (-K e^{-θ x}) - ε ≤ P(Mₙ ≤ log n / θ + x) ≤ exp (-K e^{-θ (x + h)}) + ε`, `K = C / A`. -/
theorem LatticeRenewalInput.eventually_bounds_ofLadder [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {θ h : ℝ} (hX : CramerScores P X θ) (hh : 0 < h)
    (hlat : ∀ i, ∀ᵐ ω ∂P, ∃ k : ℤ, X i ω = k * h) (L : LadderInput P (maxSegmentScoreRV X))
    (hlatY : ∀ i, ∀ᵐ ω ∂P, ∃ k : ℤ, L.Y i ω = k * h) (R : LatticeLadderRenewalData P (L.Y 0) θ h)
    (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Real.exp (-(R.tailConst / L.A * Real.exp (-(θ * x)))) - ε ≤
        P.real {ω | maxSegmentScoreRV X n ω ≤ Real.log n / θ + x} ∧
      P.real {ω | maxSegmentScoreRV X n ω ≤ Real.log n / θ + x} ≤
        Real.exp (-(R.tailConst / L.A * Real.exp (-(θ * (x + h))))) + ε :=
  (LatticeRenewalInput.ofLadder hX hh hlat L hlatY R).eventually_bounds x hε

end Assembly

end Cslib.Bioinformatics.Alignment.ScoreSignificance

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.BenjaminiHochberg

/-!
# Multiple testing for tail-calibrated rare-variant association tests

A rare-variant association scan runs one test per gene (or region) `i ∈ Fin m`. Each test
computes a statistic `T i` that is large under association and reports the p-value
`G i (T i ω)`, where `G i : ℝ → ℝ` is a *reference upper-tail function*: the upper tail of the
distribution the analyst uses as the null for `T i`. This covers

* burden tests: `T i` is the squared standardized collapsed score and `G i` a `χ²₁` upper tail;
* SKAT-type variance-component tests: `T i` is the quadratic form `Q` and `G i` the upper tail of
  the weighted `χ²₁` mixture used to calibrate it;
* genomic-control (GC) calibrated tests: `T i = S i / λ` for a raw statistic `S i` and an
  inflation factor `λ`, and `G i` is the `χ²₁` upper tail.

None of these reference tails is the exact null law in finite samples, so the file assumes
calibration rather than deriving it.

## The class of procedures (`IsTailCalibratedFamily`)

A family `(T, G)` with set of true nulls `H0 : Finset (Fin m)` (genes with no association) is
*tail-calibrated* under `μ` when

1. every statistic `T i` is measurable;
2. every reference tail `G i` is antitone (a larger statistic is more significant);
3. **per-test validity**: for every null gene `i ∈ H0` and every cutoff `s`, the reference tail
   dominates the true null tail, `μ {s ≤ T i} ≤ G i s`. For a GC test this is the statement that
   the inflation factor `λ` removes all of the inflation; when it is too small (or not applied)
   the condition fails. In practice `λ̂` is estimated from all genes' statistics, so
   `T i = S i / λ̂`; the structure still applies, but calibration of `S i / λ̂` does not follow
   from calibration with the true `λ` and must be assumed for `S i / λ̂` itself.

Condition 3 makes each null p-value valid (super-uniform), `isValidPValue_of_tail_le`; it is
the continuous-statistic analogue of the exact discrete tail p-value of
`MathlibExt.Probability.Statistics.ExactTests.TailPValue`. Nothing is assumed about non-null
genes beyond (1) and (2).

The **dependence hypothesis** is PRDS of the p-value vector on `H0`
(`MathlibExt.Probability.Statistics.MultipleTesting.IsPRDSOn`). It holds when the gene-level
statistics are independent (`isPRDSOn_tailPValue_of_iIndepFun`), e.g. genes in distinct
linkage-disequilibrium blocks with disjoint variant sets, and for perfectly comonotone
statistics. A shared estimated GC factor `λ̂` couples all genes, so the independence route does
not apply to GC-rescaled statistics and PRDS has to be argued separately. Whether a given scan
satisfies PRDS is a modeling question; nothing here asserts it for LD-correlated genes.

## Guarantees

* **Multiple-testing guarantee** (`integral_fdp_bhRejections_tailPValue_le`): if the family is
  tail-calibrated and its p-values are PRDS on `H0`, the Benjamini–Hochberg procedure at level
  `q ∈ [0, 1]` controls the false discovery rate: `E[FDP] ≤ q |H0| / m ≤ q`. This composes the
  Benjamini–Yekutieli PRDS theorem of the repository; BH is not reproved.
* **Uncertainty guarantee** (`measure_fdp_bhRejections_tailPValue_lt_ge`): under the same
  hypotheses, for `q ∈ (0, 1]` and `δ > 0`, the event that the false discovery proportion of the
  BH-selected gene set is below the fixed number `q / δ` has probability at least `1 - δ`. It
  follows from the FDR bound by Markov's inequality
  (`measure_le_fdp_bhRejections_tailPValue_le`, which gives the sharper level `q |H0| / (m δ)`);
  it is informative only when `δ > q`, since the FDP never exceeds `1`.

Both guarantees are conditional: they say nothing when a null test is anti-conservative or the
dependence is outside PRDS. The test file exhibits a single anti-conservative null test (an
uncorrected inflated statistic) for which the FDR of BH exceeds `q |H0| / m`.

## Reuse and sources (API-00 receipt)

Fresh reuse search on `origin/main` at `53666a3c1` (2026-11-11): no rare-variant, burden, SKAT or
genomic-control declarations exist in `MathlibExt`, `WantedExt` or `MathlibExtTest`, and there is
no validity lemma for a real statistic read through a dominating reference tail. Reused as is:

* `MathlibExt.Probability.Statistics.MultipleTesting.Basic`: `IsValidPValue`, `numBelow`,
  `falseDiscoveryProportion` and its bounds.
* `MathlibExt.Probability.Statistics.MultipleTesting.BenjaminiHochberg`: `bhRejections`,
  `bhIndex`, `IsPRDSOn`, `isPRDSOn_of_iIndepFun`,
  `integral_falseDiscoveryProportion_bhRejections_le_of_isPRDSOn` (Benjamini–Yekutieli 2001,
  Theorem 1.2), and `measurable_falseDiscoveryProportion_bhRejections`, used for Markov's
  inequality.

The sibling burden/SKAT and genomic-control developments are not imported; their procedures
enter only through the hypotheses of `IsTailCalibratedFamily`.

## References

* Y. Benjamini and Y. Hochberg, *Controlling the false discovery rate: a practical and powerful
  approach to multiple testing*, J. R. Statist. Soc. B 57 (1995), 289–300, Theorem 1.
* Y. Benjamini and D. Yekutieli, *The control of the false discovery rate in multiple testing
  under dependency*, Ann. Statist. 29 (2001), 1165–1188, Theorem 1.2.
* B. Devlin and K. Roeder, *Genomic control for association studies*, Biometrics 55 (1999),
  997–1004.
* B. Li and S. M. Leal, *Methods for detecting associations with rare variants for common
  diseases: application to analysis of sequence data*, Am. J. Hum. Genet. 83 (2008), 311–321.
* M. C. Wu, S. Lee, T. Cai, Y. Li, M. Boehnke and X. Lin, *Rare-variant association testing for
  sequencing data with the sequence kernel association test*, Am. J. Hum. Genet. 89 (2011),
  82–93.
* E. L. Lehmann and J. P. Romano, *Testing Statistical Hypotheses*, 3rd ed., Springer (2005),
  Lemma 3.3.1.
-/

@[expose] public section

namespace MathlibExt.Biology.StatisticalGenetics.RareVariantInference.MultipleTesting

open MeasureTheory ProbabilityTheory Filter Topology
open MathlibExt.Probability.Statistics.MultipleTesting

variable {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}

/-! ### One test: a dominating reference tail gives a valid p-value -/

/-- **Validity from a dominating reference tail.** Let a test reject for large values of a
statistic `T` and report `G (T ω)`, where `G` is antitone. If `G` dominates the null tail of `T`,
`μ {s ≤ T} ≤ G s` for every `s`, then `G ∘ T` is a valid p-value: `μ {G ∘ T ≤ t} ≤ t` for
`t ∈ [0, 1]`. No measurability or continuity is needed.

The event `{G (T ω) ≤ t}` is `{T ∈ A}` for the upper set `A = {s | G s ≤ t}`, which is either
empty, `[a, ∞)`, `(a, ∞)` or `ℝ`; in the last two cases it is an increasing union of events
`{s_n ≤ T}` with `s_n ∈ A`, and continuity from below finishes.

Source: Lehmann–Romano (2005), Lemma 3.3.1, stated there for the exact tail. -/
theorem isValidPValue_of_tail_le {μ : Measure Ω} {T : Ω → ℝ} {G : ℝ → ℝ} (hG : Antitone G)
    (htail : ∀ s, μ {ω | s ≤ T ω} ≤ ENNReal.ofReal (G s)) :
    IsValidPValue μ fun ω => G (T ω) := by
  intro t _
  set A : Set ℝ := {s | G s ≤ t} with hAdef
  have hA : IsUpperSet A := fun x y hxy hx => (hG hxy).trans hx
  have hset : {ω | G (T ω) ≤ t} = T ⁻¹' A := rfl
  have hkey : ∀ s ∈ A, μ {ω | s ≤ T ω} ≤ ENNReal.ofReal t := fun s hs =>
    (htail s).trans (ENNReal.ofReal_le_ofReal hs)
  have hseq : ∀ u : ℕ → ℝ, Antitone u → (∀ n, u n ∈ A) → (∀ x ∈ A, ∃ n, u n ≤ x) →
      μ (T ⁻¹' A) ≤ ENNReal.ofReal t := by
    intro u hu huA hcov
    have hU : T ⁻¹' A = ⋃ n, {ω | u n ≤ T ω} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq]
      exact ⟨fun h => hcov _ h, fun ⟨n, hn⟩ => hA hn (huA n)⟩
    have hmono : Monotone fun n => {ω | u n ≤ T ω} := fun i j hij ω (hω : u i ≤ T ω) =>
      (hu hij).trans hω
    rw [hU, hmono.measure_iUnion]
    exact iSup_le fun n => hkey _ (huA n)
  rw [hset]
  rcases A.eq_empty_or_nonempty with hAe | hAne
  · simp [hAe]
  by_cases hbdd : BddBelow A
  · by_cases hmem : sInf A ∈ A
    · exact hseq (fun _ => sInf A) antitone_const (fun _ => hmem)
        fun x hx => ⟨0, csInf_le hbdd hx⟩
    · obtain ⟨u, hu, hlim, huA⟩ := exists_seq_tendsto_sInf hAne hbdd
      refine hseq u hu huA fun x hx => ?_
      have hlt : sInf A < x :=
        lt_of_le_of_ne (csInf_le hbdd hx) fun h => hmem (h ▸ hx)
      obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hlt)).exists
      exact ⟨n, hn.le⟩
  · have hneg : ∀ n : ℕ, -(n : ℝ) ∈ A := by
      intro n
      rw [not_bddBelow_iff] at hbdd
      obtain ⟨y, hy, hlt⟩ := hbdd (-(n : ℝ))
      exact hA hlt.le hy
    refine hseq (fun n => -(n : ℝ)) (fun i j h => by simpa using h) hneg fun x _ => ?_
    obtain ⟨n, hn⟩ := exists_nat_ge (-x)
    exact ⟨n, by linarith⟩

/-! ### The class of tail-calibrated test families -/

/-- The p-values of a family of `m` gene-level tests: test `i` reports `G i (T i ω)`, its
reference upper tail evaluated at its statistic. -/
def tailPValue (T : Fin m → Ω → ℝ) (G : Fin m → ℝ → ℝ) : Fin m → Ω → ℝ :=
  fun i ω => G i (T i ω)

/-- **Tail-calibrated family of association tests** with true nulls `H0`: every statistic is
measurable, every reference tail is antitone, and for every null gene the reference tail
dominates the true null tail of its statistic, `μ {s ≤ T i} ≤ G i s`. Burden and SKAT-type
tests with a conservative reference null, and genomic-control tests whose inflation factor
removes all of the inflation, are of this form. -/
structure IsTailCalibratedFamily (μ : Measure Ω) (T : Fin m → Ω → ℝ) (G : Fin m → ℝ → ℝ)
    (H0 : Finset (Fin m)) : Prop where
  /-- Every statistic is measurable. -/
  measurable_stat : ∀ i, Measurable (T i)
  /-- Every reference upper tail is antitone. -/
  antitone_refTail : ∀ i, Antitone (G i)
  /-- Per-test validity: for a null gene the reference tail dominates the true null tail. -/
  null_tail_le : ∀ i ∈ H0, ∀ s, μ {ω | s ≤ T i ω} ≤ ENNReal.ofReal (G i s)

namespace IsTailCalibratedFamily

variable {μ : Measure Ω} {T : Fin m → Ω → ℝ} {G : Fin m → ℝ → ℝ} {H0 : Finset (Fin m)}

/-- The p-values of a tail-calibrated family are measurable. -/
theorem measurable_tailPValue (h : IsTailCalibratedFamily μ T G H0) (i : Fin m) :
    Measurable (tailPValue T G i) :=
  (h.antitone_refTail i).measurable.comp (h.measurable_stat i)

/-- The null p-values of a tail-calibrated family are valid. -/
theorem isValidPValue (h : IsTailCalibratedFamily μ T G H0) {i : Fin m} (hi : i ∈ H0) :
    IsValidPValue μ (tailPValue T G i) :=
  isValidPValue_of_tail_le (h.antitone_refTail i) (h.null_tail_le i hi)

end IsTailCalibratedFamily

/-- **Independent statistics give PRDS p-values.** If the gene-level statistics of a
tail-calibrated family are mutually independent, its p-values are PRDS on every set `H0'` (only
the measurability part of the calibration hypothesis is used). -/
theorem isPRDSOn_tailPValue_of_iIndepFun {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Fin m → Ω → ℝ} {G : Fin m → ℝ → ℝ} {H0 : Finset (Fin m)}
    (h : IsTailCalibratedFamily μ T G H0) (hindep : iIndepFun T μ) (H0' : Finset (Fin m)) :
    IsPRDSOn μ (tailPValue T G) H0' :=
  isPRDSOn_of_iIndepFun μ _ h.measurable_tailPValue
    (hindep.comp G fun i => (h.antitone_refTail i).measurable) H0'

/-! ### The guarantees -/

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Fin m → Ω → ℝ} {G : Fin m → ℝ → ℝ}
  {H0 : Finset (Fin m)}

/-- **FDR control for tail-calibrated rare-variant tests.** If the family `(T, G)` is
tail-calibrated with true nulls `H0` (`IsTailCalibratedFamily`: measurable statistics, antitone
reference tails, and for every null gene a reference tail dominating the true null tail) and its
p-values are PRDS on `H0`, then the Benjamini–Hochberg procedure at level `q ∈ [0, 1]` has false
discovery rate at most `q |H0| / m`.

Source: Benjamini & Yekutieli (2001), Theorem 1.2, applied through
`integral_falseDiscoveryProportion_bhRejections_le_of_isPRDSOn`. -/
theorem integral_fdp_bhRejections_tailPValue_le (h : IsTailCalibratedFamily μ T G H0)
    (hprds : IsPRDSOn μ (tailPValue T G) H0) {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ ω, falseDiscoveryProportion H0 (bhRejections q fun i => tailPValue T G i ω) ∂μ ≤
      q * H0.card / m :=
  integral_falseDiscoveryProportion_bhRejections_le_of_isPRDSOn μ (tailPValue T G)
    h.measurable_tailPValue H0 hprds (fun _ hi => h.isValidPValue hi) q hq₀ hq₁

/-- **FDR control for independent tail-calibrated tests.** The special case of
`integral_fdp_bhRejections_tailPValue_le` in which the gene-level statistics are mutually
independent. -/
theorem integral_fdp_bhRejections_tailPValue_le_of_iIndepFun (h : IsTailCalibratedFamily μ T G H0)
    (hindep : iIndepFun T μ) {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ ω, falseDiscoveryProportion H0 (bhRejections q fun i => tailPValue T G i ω) ∂μ ≤
      q * H0.card / m :=
  integral_fdp_bhRejections_tailPValue_le h (isPRDSOn_tailPValue_of_iIndepFun h hindep H0) hq₀ hq₁

/-- The bound `q |H0| / m` is at most `q`. -/
theorem mul_card_div_le {q : ℝ} (hq₀ : 0 ≤ q) (H0 : Finset (Fin m)) :
    q * H0.card / m ≤ q := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [hq₀]
  rw [mul_div_assoc]
  refine mul_le_of_le_one_right hq₀ ((div_le_one (by positivity)).2 ?_)
  exact_mod_cast (Finset.card_le_univ H0).trans_eq (Fintype.card_fin m)

/-- **Markov bound on the false discovery proportion.** Under the hypotheses of
`integral_fdp_bhRejections_tailPValue_le`, for every `c > 0` the probability that the BH-selected
gene set has false discovery proportion at least `c` is at most `q |H0| / (m c)`. -/
theorem measure_le_fdp_bhRejections_tailPValue_le (h : IsTailCalibratedFamily μ T G H0)
    (hprds : IsPRDSOn μ (tailPValue T G) H0) {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) {c : ℝ}
    (hc : 0 < c) :
    μ {ω | c ≤ falseDiscoveryProportion H0 (bhRejections q fun i => tailPValue T G i ω)} ≤
      ENNReal.ofReal (q * H0.card / m / c) := by
  set F := fun ω => falseDiscoveryProportion H0 (bhRejections q fun i => tailPValue T G i ω)
  have hFm : Measurable F :=
    measurable_falseDiscoveryProportion_bhRejections _ h.measurable_tailPValue H0 q
  have hFint : Integrable F μ :=
    Integrable.of_bound hFm.aestronglyMeasurable 1 (Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (falseDiscoveryProportion_nonneg _ _)]
      exact falseDiscoveryProportion_le_one _ _)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall fun ω => falseDiscoveryProportion_nonneg _ _) hFint c
  have hFDR := integral_fdp_bhRejections_tailPValue_le h hprds hq₀ hq₁
  rw [← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [le_div_iff₀ hc, mul_comm]
  exact hmarkov.trans hFDR

/-- **Probability bound on the false discovery proportion of the BH-selected set.** Under the
hypotheses of `integral_fdp_bhRejections_tailPValue_le` (tail-calibrated tests with PRDS
p-values), for `q ∈ (0, 1]` and `δ > 0`, the event that the gene set selected by BH at level `q`
has false discovery proportion below the fixed number `q / δ` has probability at least `1 - δ`.
The statement is informative only for `δ > q`, since the FDP is at most `1`;
`measure_le_fdp_bhRejections_tailPValue_le` gives the sharper level `q |H0| / (m δ)`. -/
theorem measure_fdp_bhRejections_tailPValue_lt_ge (h : IsTailCalibratedFamily μ T G H0)
    (hprds : IsPRDSOn μ (tailPValue T G) H0) {q : ℝ} (hq₀ : 0 < q) (hq₁ : q ≤ 1) {δ : ℝ}
    (hδ₀ : 0 < δ) :
    ENNReal.ofReal (1 - δ) ≤
      μ {ω | falseDiscoveryProportion H0 (bhRejections q fun i => tailPValue T G i ω) < q / δ} := by
  set F := fun ω => falseDiscoveryProportion H0 (bhRejections q fun i => tailPValue T G i ω)
  have hFm : Measurable F :=
    measurable_falseDiscoveryProportion_bhRejections _ h.measurable_tailPValue H0 q
  have hc : 0 < q / δ := div_pos hq₀ hδ₀
  have hS : MeasurableSet {ω | q / δ ≤ F ω} := measurableSet_le measurable_const hFm
  have hcompl : {ω | F ω < q / δ} = {ω | q / δ ≤ F ω}ᶜ := by
    ext ω
    simp
  have hle : μ {ω | q / δ ≤ F ω} ≤ ENNReal.ofReal δ := by
    refine (measure_le_fdp_bhRejections_tailPValue_le h hprds hq₀.le hq₁ hc).trans
      (ENNReal.ofReal_le_ofReal ?_)
    calc q * H0.card / m / (q / δ) ≤ q / (q / δ) := by
          gcongr
          exact mul_card_div_le hq₀.le H0
      _ = δ := by field_simp
  change ENNReal.ofReal (1 - δ) ≤ μ {ω | F ω < q / δ}
  rw [hcompl, prob_compl_eq_one_sub hS, ENNReal.ofReal_sub 1 hδ₀.le, ENNReal.ofReal_one]
  exact tsub_le_tsub_left hle 1

end MathlibExt.Biology.StatisticalGenetics.RareVariantInference.MultipleTesting

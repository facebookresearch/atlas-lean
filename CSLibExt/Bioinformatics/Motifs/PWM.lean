/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Round
public import Mathlib.Data.Finsupp.Basic
public import MathlibExt.InformationTheory.FiniteEntropy
public import MathlibExt.Probability.Statistics.NeymanPearson
public import CSLibExt.MachineLearning.LatentVariable.ExpectationMaximization
import CSLibExt.MachineLearning.LatentVariable.BernoulliMixture

/-!
# Position weight matrices

A position weight matrix (PWM) models a binding site of width `w` over a finite alphabet `α` as
`w` independent columns: the site model `p : Fin w → α → ℝ` gives each column a letter
distribution, and sites are scored against a background `q : α → ℝ` of independent letters.

## Main results

* Scores (Staden 1989; Stormo 2000). `score_logOdds`: the log-odds score
  `∑ᵢ log (p i (s i) / q (s i))` is the log-likelihood ratio of the product site model against
  the background. `sum_mul_siteLik_le_of_sum_mul_bgLik_le`: thresholding it is the most powerful
  test of its size (an instance of the Neyman–Pearson lemma).
* Information content (Schneider, Stormo, Gold and Ehrenfeucht 1986). `infoContent_eq_klDiv`:
  the information content of a column is `KL(pᵢ ‖ q)` in bits; `infoContent_nonneg`;
  `infoContent_uniform`: against the uniform background it is `log₂ |α| - H(pᵢ)`, hence at most
  `2` bits for DNA (`infoContent_uniform_le_two`). `sum_siteLik_mul_score_logOdds`: the expected
  log-odds score of a site is `log 2` times the total information content.
* Exact score distributions (Staden 1989; Touzet and Varré 2007). For an integer matrix, the
  column-by-column convolution `scoreDist` computes the exact background distribution of the
  score (`scoreDist_apply`) and so exact p-values (`pValue_eq`); `abs_score_sub_score_round_le`
  bounds the error of scaling and rounding a real matrix.
* Berg–von Hippel (1987). `selectedLaw_eq_siteLik`: selecting background sites with weight
  `e^{-λ E(s)}` for an additive energy `E` gives the product site model `boltzmannPWM`, and
  `logOdds_boltzmannPWM`: its log-odds are `-λ ε i b - log Zᵢ`.
* Motif-finding EM. `motifJoint` covers the one-occurrence-per-sequence (OOPS) model of
  Lawrence and Reilly (1990) and the zero-or-one-occurrence (ZOOPS) model of MEME (Bailey and
  Elkan 1994, 1995); `motifJoint_of_start_eq_some` shows it is the window model.
  `posterior_motifModel` is the closed E-step, `emQ_le_emQ_mStep` shows that the expected-count
  M-step `mStep` maximizes the EM objective, and `logLik_iterate_mStep_monotone` that the
  likelihood is nondecreasing along the iterates (an instance of the generic EM theorem).
* Karlin–Altschul `λ` (Karlin and Altschul 1990; Altschul 1991). `existsUnique_pairMGF_eq_one`:
  for a score matrix with negative expected score and a positive entry there is a unique
  `λ > 0` with `∑ pₐ p_b e^{λ s_{ab}} = 1`; `isDist_targetFreq`, `score_eq_log_targetFreq` and
  `relEntropy_eq_and_nonneg`: the matrix is a log-odds matrix for the implicit target
  frequencies `q_{ab} = pₐ p_b e^{λ s_{ab}}`, with relative entropy `λ ∑ q s ≥ 0`;
  `sum_targetFreq_mul_pos`: the expected score under the targets is positive.

Not covered: the E-value statistics `E = K m n e^{-λ S}` of local alignment scores, MEME's
re-estimation of the background and of the occurrence probability `γ`, its Dirichlet priors,
and its two-component mixture (MM/TCM) model.

## Cost model

`scoreStep` convolves a finitely supported distribution with one column: `|α|` shifted copies,
`O(|α| R)` operations for a support of size `R`, so `scoreDist` costs `O(w |α| R)` where `R` is
the range of the integer scores. In Lean it is a mathematical (classical) `Finsupp` definition.

## References

* R. Staden, *Methods for calculating the probabilities of finding patterns in sequences*,
  CABIOS 5 (1989), 89–96.
* T. D. Schneider, G. D. Stormo, L. Gold and A. Ehrenfeucht, *Information content of binding
  sites on nucleotide sequences*, J. Mol. Biol. 188 (1986), 415–431.
* G. D. Stormo, *DNA binding sites: representation and discovery*, Bioinformatics 16 (2000),
  16–23.
* H. Touzet and J.-S. Varré, *Efficient and accurate P-value computation for Position Weight
  Matrices*, Algorithms Mol. Biol. 2 (2007), 15.
* O. G. Berg and P. H. von Hippel, *Selection of DNA binding sites by regulatory proteins.
  Statistical-mechanical theory and application to operators and promoters*, J. Mol. Biol. 193
  (1987), 723–750.
* C. E. Lawrence and A. A. Reilly, *An expectation maximization (EM) algorithm for the
  identification and characterization of common sites in unaligned biopolymer sequences*,
  Proteins 7 (1990), 41–51.
* T. L. Bailey and C. Elkan, *Fitting a mixture model by expectation maximization to discover
  motifs in biopolymers*, Proc. ISMB 2 (1994), 28–36; *Unsupervised learning of multiple motifs
  in biopolymers using expectation maximization*, Machine Learning 21 (1995), 51–80.
* S. Karlin and S. F. Altschul, *Methods for assessing the statistical significance of
  molecular sequence features by using general scoring schemes*, PNAS 87 (1990), 2264–2268.
* S. F. Altschul, *Amino acid substitution matrices from an information theoretic
  perspective*, J. Mol. Biol. 219 (1991), 555–565.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Bioinformatics.Motifs.PWM

open Real Finset
open Cslib.MachineLearning.LatentVariable.ExpectationMaximization

variable {α : Type*} [Fintype α] {w : ℕ}

/-! ## Scores and likelihoods -/

/-- The score `∑ᵢ W i (s i)` of a site `s` of width `w` under a position weight matrix `W`. -/
def score {R : Type*} [AddCommMonoid R] (W : Fin w → α → R) (s : Fin w → α) : R :=
  ∑ i, W i (s i)

/-- The likelihood `∏ᵢ p i (s i)` of a site under the product (column-independent) site model
`p`. -/
def siteLik (p : Fin w → α → ℝ) (s : Fin w → α) : ℝ := ∏ i, p i (s i)

/-- The likelihood `∏ₖ q (x k)` of a sequence of length `m` under the background of independent
letters with law `q`. -/
def bgLik {m : ℕ} (q : α → ℝ) (x : Fin m → α) : ℝ := ∏ k, q (x k)

/-- The log-odds matrix `log (p i b / q b)` of a site model against a background (natural
logarithm). -/
noncomputable def logOdds (p : Fin w → α → ℝ) (q : α → ℝ) : Fin w → α → ℝ :=
  fun i b => log (p i b / q b)

omit [Fintype α] in
/-- **The log-odds score is a log-likelihood ratio** (Staden 1989; Stormo 2000): for positive
site model and background, `score (logOdds p q) s = log (siteLik p s / bgLik q s)`. -/
theorem score_logOdds {p : Fin w → α → ℝ} {q : α → ℝ} (hp : ∀ i b, 0 < p i b)
    (hq : ∀ b, 0 < q b) (s : Fin w → α) :
    score (logOdds p q) s = log (siteLik p s / bgLik q s) := by
  have hsl : ∀ i ∈ univ, p i (s i) ≠ 0 := fun i _ => (hp i (s i)).ne'
  have hbg : ∀ i ∈ univ, q (s i) ≠ 0 := fun i _ => (hq (s i)).ne'
  rw [siteLik, bgLik, log_div (prod_ne_zero_iff.2 hsl) (prod_ne_zero_iff.2 hbg), log_prod hsl,
    log_prod hbg, ← sum_sub_distrib]
  exact sum_congr rfl fun i _ => log_div (hp i (s i)).ne' (hq (s i)).ne'

/-- A product of column distributions is a distribution on sites. -/
theorem sum_siteLik {p : Fin w → α → ℝ} (hp : ∀ i, IsDist (p i)) :
    ∑ s, siteLik p s = 1 := by
  simp only [siteLik]
  rw [← Fintype.prod_sum]
  simp [fun i => (hp i).2]

/-- The background law of independent letters is a distribution on sequences. -/
theorem sum_bgLik {m : ℕ} {q : α → ℝ} (hq : IsDist q) : ∑ x : Fin m → α, bgLik q x = 1 := by
  simp only [bgLik]
  rw [← Fintype.prod_sum]
  simp [hq.2]

/-- **Thresholding the log-odds score is most powerful** (Neyman–Pearson): a test `φ` of the
background (null) against the site model whose background size is at most that of the
threshold test `score > t` has at most its power. -/
theorem sum_mul_siteLik_le_of_sum_mul_bgLik_le {p : Fin w → α → ℝ} {q : α → ℝ}
    (hp : ∀ i b, 0 < p i b) (hq : ∀ b, 0 < q b) (t : ℝ) (φ : (Fin w → α) → ℝ)
    (hφ0 : ∀ s, 0 ≤ φ s) (hφ1 : ∀ s, φ s ≤ 1)
    (hsize : ∑ s, φ s * bgLik q s ≤
      ∑ s, (if t < score (logOdds p q) s then 1 else 0) * bgLik q s) :
    ∑ s, φ s * siteLik p s ≤
      ∑ s, (if t < score (logOdds p q) s then 1 else 0) * siteLik p s := by
  classical
  let _ : MeasurableSpace (Fin w → α) := ⊤
  have : MeasurableSingletonClass (Fin w → α) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  set T : (Fin w → α) → ℝ := fun s => if t < score (logOdds p q) s then 1 else 0 with hT
  have hT01 : ∀ s, T s ∈ Set.Icc (0 : ℝ) 1 := fun s => by
    simp only [hT]; split_ifs <;> norm_num
  have hsite : ∀ s, 0 < siteLik p s := fun s => prod_pos fun i _ => hp i (s i)
  have hbg : ∀ s : Fin w → α, 0 < bgLik q s := fun s => prod_pos fun i _ => hq (s i)
  -- `score > t` iff `siteLik > e^t · bgLik`
  have hiff : ∀ s, t < score (logOdds p q) s ↔ exp t * bgLik q s < siteLik p s := fun s => by
    rw [score_logOdds hp hq, lt_log_iff_exp_lt (div_pos (hsite s) (hbg s)),
      lt_div_iff₀ (hbg s)]
  have hint : ∀ f : (Fin w → α) → ℝ,
      ∫ x, f x ∂MeasureTheory.Measure.count = ∑ x, f x := fun f => by
    rw [MeasureTheory.integral_fintype MeasureTheory.Integrable.of_finite]
    simp [MeasureTheory.measureReal_def]
  have key := MathlibExt.Probability.Statistics.NeymanPearson.neyman_pearson_dominated_two_simple
    (μ := MeasureTheory.Measure.count) (p := bgLik q) (q := siteLik p)
    measurable_from_top measurable_from_top (fun s => (hbg s).le) (fun s => (hsite s).le)
    MeasureTheory.Integrable.of_finite MeasureTheory.Integrable.of_finite (exp t)
    (exp_pos t).le (fun s => ⟨T s, hT01 s⟩) measurable_from_top
    (fun s hs => by change T s = 1; simp only [hT]; rw [ite_eq_left ((hiff s).2 hs)])
    (fun s hs => by
      change T s = 0; simp only [hT]; rw [ite_eq_right fun h => lt_asymm ((hiff s).1 h) hs])
    (fun s => ⟨φ s, hφ0 s, hφ1 s⟩) measurable_from_top
  simp only [hint] at key
  exact key hsize

/-! ## Information content -/

/-- The information content `∑_b p b log₂ (p b / q b)` (in bits) of a PWM column `p` against
the background `q` (Schneider et al. 1986). Letters with `p b = 0` contribute `0`. -/
noncomputable def infoContent (p q : α → ℝ) : ℝ := (∑ b, p b * log (p b / q b)) / log 2

/-- **Information content is a Kullback–Leibler divergence**: for laws `P ≪ Q`, the information
content of `P` against `Q` is `KL(P ‖ Q) / log 2`, Mathlib's `klDiv` in bits. -/
theorem infoContent_eq_klDiv [MeasurableSpace α] [MeasurableSingletonClass α] (P Q : PMF α)
    (hPQ : ∀ a, Q a = 0 → P a = 0) :
    infoContent (fun b => (P b).toReal) (fun b => (Q b).toReal) =
      (InformationTheory.klDiv P.toMeasure Q.toMeasure).toReal / log 2 := by
  rw [InformationTheory.toReal_klDiv_toMeasure hPQ, infoContent]

/-- **Information content is nonnegative** (Gibbs' inequality) for a column distribution and a
positive background distribution. -/
theorem infoContent_nonneg {p q : α → ℝ} (hp : IsDist p) (hq : IsDist q)
    (hq0 : ∀ b, 0 < q b) : 0 ≤ infoContent p q := by
  refine div_nonneg ?_ (log_pos one_lt_two).le
  have h := sum_mul_log_sub_le (p := q) (q := p) hq0 hp
  rw [hq.2, log_one] at h
  have hterm : ∀ b, p b * log (p b / q b) = -(p b * (log (q b) - log (p b))) := by
    intro b
    rcases (hp.1 b).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · rw [log_div hpos.ne' (hq0 b).ne']; ring
  simp only [hterm, sum_neg_distrib]
  linarith

/-- **Information content against the uniform background** (Schneider et al. 1986):
`log₂ |α| - H(p)`, the maximal entropy minus the column entropy. -/
theorem infoContent_uniform [Nonempty α] (P : PMF α) :
    infoContent (fun b => (P b).toReal) (fun _ => ((Fintype.card α : ℝ))⁻¹) =
      logb 2 (Fintype.card α) - InformationTheory.shannonEntropy P := by
  have hsum : ∑ b, (P b).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun b _ => P.apply_ne_top b),
      ← tsum_fintype (L := SummationFilter.unconditional _), P.tsum_coe,
      ENNReal.toReal_one]
  have hc : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hterm : ∀ b, (P b).toReal * log ((P b).toReal / ((Fintype.card α : ℝ))⁻¹) =
      (P b).toReal * log (Fintype.card α) - negMulLog (P b).toReal := by
    intro b
    rcases ENNReal.toReal_nonneg.eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · rw [div_inv_eq_mul, log_mul hpos.ne' hc.ne', negMulLog]; ring
  rw [infoContent, InformationTheory.shannonEntropy, logb, ← sub_div]
  congr 1
  rw [sum_congr rfl fun b _ => hterm b, sum_sub_distrib, ← sum_mul, hsum, one_mul]

/-- Against the uniform background, a column carries at most `log₂ |α|` bits. -/
theorem infoContent_uniform_le [Nonempty α] (P : PMF α) :
    infoContent (fun b => (P b).toReal) (fun _ => ((Fintype.card α : ℝ))⁻¹) ≤
      logb 2 (Fintype.card α) := by
  rw [infoContent_uniform]
  linarith [InformationTheory.shannonEntropy_nonneg P]

/-- For a four-letter alphabet (DNA) and the uniform background, a column carries between `0`
and `2` bits. -/
theorem infoContent_uniform_le_two [Nonempty α] (h4 : Fintype.card α = 4) (P : PMF α) :
    infoContent (fun b => (P b).toReal) (fun _ => ((Fintype.card α : ℝ))⁻¹) ≤ 2 := by
  have h := infoContent_uniform_le P
  have h2 : logb 2 (Fintype.card α) = 2 := by
    rw [h4, show ((4 : ℕ) : ℝ) = 2 ^ (2 : ℕ) by norm_num, logb_pow, logb_self_eq_one one_lt_two]
    norm_num
  linarith

/-- The site-model expectation of a function of one column is its column expectation. -/
private lemma sum_siteLik_mul_apply {p : Fin w → α → ℝ} (hp : ∀ i, ∑ b, p i b = 1)
    (j : Fin w) (g : α → ℝ) : ∑ s, siteLik p s * g (s j) = ∑ b, p j b * g b := by
  classical
  have h : ∀ s : Fin w → α, siteLik p s * g (s j) =
      ∏ i, (if i = j then p i (s i) * g (s i) else p i (s i)) := by
    intro s
    rw [siteLik, ← mul_prod_erase univ (fun i => p i (s i)) (mem_univ j),
      ← mul_prod_erase univ _ (mem_univ j), ite_eq_left rfl,
      prod_congr rfl fun i hi => ite_eq_right (ne_of_mem_erase hi)]
    ring
  simp_rw [h]
  rw [← Fintype.prod_sum (fun i b => if i = j then p i b * g b else p i b)]
  rw [prod_congr rfl fun i _ => (show (∑ b, if i = j then p i b * g b else p i b) =
      if i = j then ∑ b, p j b * g b else 1 by
    split_ifs with hij
    · subst hij; rfl
    · exact hp i), prod_ite_eq' univ j, ite_eq_left (mem_univ j)]

/-- **The expected log-odds score is the total information content**: under the site model,
`E[score] = log 2 · ∑ᵢ IC(pᵢ ‖ q)`. This is an identity for every `q` (both sides use the same
logarithms); it is an expected log-likelihood ratio for a positive background. -/
theorem sum_siteLik_mul_score_logOdds {p : Fin w → α → ℝ} {q : α → ℝ}
    (hp : ∀ i, IsDist (p i)) :
    ∑ s, siteLik p s * score (logOdds p q) s = log 2 * ∑ i, infoContent (p i) q := by
  simp only [score, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_siteLik_mul_apply (fun i => (hp i).2) i (logOdds p q i), infoContent,
    mul_div_cancel₀ _ (log_pos one_lt_two).ne']
  rfl

/-! ## Exact score distribution of an integer matrix -/

/-- One column of the score-distribution recursion: from the distribution `d` of the score of
the first columns, the distribution after adding a column `c` with background `q`,
`∑_b q b · (d shifted by c b)`. -/
noncomputable def scoreStep (q : α → ℝ) (d : ℤ →₀ ℝ) (c : α → ℤ) : ℤ →₀ ℝ :=
  ∑ b, q b • d.mapDomain (· + c b)

/-- The background distribution of the score of an integer matrix `M`, computed column by column
from the point mass at `0` (Staden 1989; Touzet and Varré 2007). -/
noncomputable def scoreDist (q : α → ℝ) (M : Fin w → α → ℤ) : ℤ →₀ ℝ :=
  (List.ofFn M).foldl (scoreStep q) (Finsupp.single 0 1)

private lemma scoreStep_apply (q : α → ℝ) (d : ℤ →₀ ℝ) (c : α → ℤ) (x : ℤ) :
    scoreStep q d c x = ∑ b, q b * d (x - c b) := by
  simp only [scoreStep, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  refine sum_congr rfl fun b _ => ?_
  congr 1
  conv_lhs => rw [show x = (x - c b) + c b by ring]
  exact Finsupp.mapDomain_apply_of_injective (add_left_injective (c b)) d (x - c b)

/-- The fold from any initial distribution `d`: `∑ₛ q(s) d (x - score M s)`. -/
private lemma foldl_scoreStep_apply (q : α → ℝ) :
    ∀ {w : ℕ} (M : Fin w → α → ℤ) (d : ℤ →₀ ℝ) (x : ℤ),
      (List.ofFn M).foldl (scoreStep q) d x = ∑ s, bgLik q s * d (x - score M s)
  | 0, M, d, x => by
    simp [bgLik, score]
  | w + 1, M, d, x => by
    rw [List.ofFn_succ, List.foldl_cons, foldl_scoreStep_apply q (fun i => M i.succ)]
    simp only [scoreStep_apply, mul_sum]
    rw [← (Fin.consEquiv fun _ : Fin (w + 1) => α).sum_comp, Fintype.sum_prod_type, sum_comm]
    refine sum_congr rfl fun b _ => sum_congr rfl fun s' _ => ?_
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, bgLik, score, Fin.prod_univ_succ,
      Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    ring_nf

/-- **The column recursion computes the exact score distribution**: `scoreDist q M t` is
`∑_{s : score M s = t} ∏ᵢ q (s i)`, for every `q`. When `q` is a distribution this is the
background probability of the score `t` (the weights sum to `1` by `sum_bgLik`). -/
theorem scoreDist_apply (q : α → ℝ) (M : Fin w → α → ℤ) (t : ℤ) :
    scoreDist q M t = ∑ s with score M s = t, bgLik q s := by
  rw [scoreDist, foldl_scoreStep_apply, sum_filter]
  refine sum_congr rfl fun s _ => ?_
  rw [Finsupp.single_apply]
  by_cases h : score M s = t
  · simp [h]
  · rw [ite_eq_right (fun h' => h (by omega)), ite_eq_right h, mul_zero]

/-- The exact p-value of the score threshold `t`, summed over the computed distribution. -/
noncomputable def pValue (q : α → ℝ) (M : Fin w → α → ℤ) (t : ℤ) : ℝ :=
  ∑ u ∈ (scoreDist q M).support with t ≤ u, scoreDist q M u

/-- **Exact p-values**: `pValue q M t = ∑_{s : score M s ≥ t} ∏ᵢ q (s i)`, the background
probability `P_q(score M ≥ t)` when `q` is a distribution. -/
theorem pValue_eq (q : α → ℝ) (M : Fin w → α → ℤ) (t : ℤ) :
    pValue q M t = ∑ s with t ≤ score M s, bgLik q s := by
  classical
  have hD : ∀ u, scoreDist q M u = ∑ s with score M s = u, bgLik q s := scoreDist_apply q M
  set T := (univ.image (score M)).filter (t ≤ ·) with hT
  have hsub : (scoreDist q M).support.filter (t ≤ ·) ⊆ T := by
    intro u hu
    rw [mem_filter, Finsupp.mem_support_iff] at hu
    refine mem_filter.2 ⟨mem_image.2 ?_, hu.2⟩
    by_contra hne
    refine hu.1 ((hD u).trans (sum_eq_zero fun s hs => ?_))
    exact absurd ⟨s, mem_univ _, (mem_filter.1 hs).2⟩ hne
  rw [pValue, sum_subset hsub fun u hu hnot => ?_]
  · rw [← sum_fiberwise_of_maps_to (s := univ.filter fun s => t ≤ score M s) (t := T)
      (g := score M) fun s hs => mem_filter.2 ⟨mem_image_of_mem _ (mem_univ s),
        (mem_filter.1 hs).2⟩]
    refine sum_congr rfl fun u hu => ?_
    rw [hD, filter_filter]
    refine sum_congr (Finset.ext fun s => ?_) fun _ _ => rfl
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro h; exact ⟨h ▸ (mem_filter.1 hu).2, h⟩
    · exact fun h => h.2
  · have htu : t ≤ u := (mem_filter.1 hu).2
    by_contra hne
    exact hnot (mem_filter.2 ⟨Finsupp.mem_support_iff.2 hne, htu⟩)

omit [Fintype α] in
/-- **Scaling and rounding error**: rounding `c · W` to integers changes the rescaled score of
every site by at most `w / (2c)`. -/
theorem abs_score_sub_score_round_le (W : Fin w → α → ℝ) {c : ℝ} (hc : 0 < c)
    (s : Fin w → α) :
    |score W s - ((score (fun i b => round (c * W i b)) s : ℤ) : ℝ) / c| ≤ w / (2 * c) := by
  have hcast : ((score (fun i b => round (c * W i b)) s : ℤ) : ℝ) =
      ∑ i, (round (c * W i (s i)) : ℝ) := by simp [score]
  have hsplit : score W s - (∑ i, (round (c * W i (s i)) : ℝ)) / c =
      (∑ i, (c * W i (s i) - round (c * W i (s i)))) / c := by
    rw [sum_sub_distrib, ← mul_sum, score]
    field_simp
  rw [hcast, hsplit, abs_div, abs_of_pos hc]
  have hle : |∑ i, (c * W i (s i) - round (c * W i (s i)))| ≤ w / 2 :=
    calc |∑ i, (c * W i (s i) - round (c * W i (s i)))|
        ≤ ∑ i, |c * W i (s i) - round (c * W i (s i))| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin w, (1 / 2 : ℝ) := sum_le_sum fun i _ => abs_sub_round _
      _ = w / 2 := by simp; ring
  rw [show (w : ℝ) / (2 * c) = (w / 2) / c by ring]
  exact div_le_div_of_nonneg_right hle hc.le

/-! ## Berg–von Hippel: Boltzmann selection gives a PWM -/

/-- The column partition function `Z = ∑_b q b e^{-λ ε b}` of energies `ε` at inverse
temperature `λ`. -/
noncomputable def partitionFn (q ε : α → ℝ) (lam : ℝ) : ℝ := ∑ b, q b * exp (-lam * ε b)

/-- The Boltzmann PWM `q b e^{-λ ε i b} / Zᵢ` of an energy matrix `ε`. -/
noncomputable def boltzmannPWM (q : α → ℝ) (ε : Fin w → α → ℝ) (lam : ℝ) : Fin w → α → ℝ :=
  fun i b => q b * exp (-lam * ε i b) / partitionFn q (ε i) lam

/-- The law of background sites selected with weight `e^{-λ E(s)}` for the additive energy
`E s = score ε s = ∑ᵢ ε i (s i)`: `q(s) e^{-λ E(s)} / ∑_{s'} q(s') e^{-λ E(s')}`. -/
noncomputable def selectedLaw (q : α → ℝ) (ε : Fin w → α → ℝ) (lam : ℝ) (s : Fin w → α) : ℝ :=
  bgLik q s * exp (-lam * score ε s) / ∑ s', bgLik q s' * exp (-lam * score ε s')

/-- The partition function of a positive background is positive. -/
theorem partitionFn_pos [Nonempty α] {q : α → ℝ} (hq : ∀ b, 0 < q b) (ε : α → ℝ) (lam : ℝ) :
    0 < partitionFn q ε lam := by
  exact sum_pos (fun b _ => mul_pos (hq b) (exp_pos _)) univ_nonempty

/-- Each column of the Boltzmann PWM is a distribution. -/
theorem isDist_boltzmannPWM [Nonempty α] {q : α → ℝ} (hq : ∀ b, 0 < q b)
    (ε : Fin w → α → ℝ) (lam : ℝ) (i : Fin w) : IsDist (boltzmannPWM q ε lam i) := by
  have hZ := partitionFn_pos hq (ε i) lam
  refine ⟨fun b => div_nonneg (mul_pos (hq b) (exp_pos _)).le hZ.le, ?_⟩
  simp only [boltzmannPWM]
  rw [← sum_div]
  exact div_self hZ.ne'

/-- **Berg–von Hippel**: Boltzmann selection of background sites with an additive energy yields
the product site model with columns `boltzmannPWM`. This is an identity for every `q`
(both sides vanish when some `Zᵢ = 0`); it is a statement about laws for positive `q`. -/
theorem selectedLaw_eq_siteLik (q : α → ℝ) (ε : Fin w → α → ℝ) (lam : ℝ) (s : Fin w → α) :
    selectedLaw q ε lam s = siteLik (boltzmannPWM q ε lam) s := by
  have hnum : ∀ s : Fin w → α, bgLik q s * exp (-lam * score ε s) =
      ∏ i, (q (s i) * exp (-lam * ε i (s i))) := by
    intro s
    simp only [bgLik, score, mul_sum, exp_sum, prod_mul_distrib]
  have hden : ∑ s' : Fin w → α, bgLik q s' * exp (-lam * score ε s') =
      ∏ i, partitionFn q (ε i) lam := by
    simp only [hnum, partitionFn]
    exact (Fintype.prod_sum (fun i b => q b * exp (-lam * ε i b))).symm
  rw [selectedLaw, hnum, hden, siteLik, ← prod_div_distrib]
  rfl

/-- **Log-odds are affine in the energies**: `log (p i b / q b) = -λ ε i b - log Zᵢ` for the
Boltzmann PWM. -/
theorem logOdds_boltzmannPWM [Nonempty α] {q : α → ℝ} (hq : ∀ b, 0 < q b)
    (ε : Fin w → α → ℝ) (lam : ℝ) (i : Fin w) (b : α) :
    logOdds (boltzmannPWM q ε lam) q i b = -lam * ε i b - log (partitionFn q (ε i) lam) := by
  have hZ := partitionFn_pos hq (ε i) lam
  simp only [logOdds, boltzmannPWM]
  rw [show q b * exp (-lam * ε i b) / partitionFn q (ε i) lam / q b =
      exp (-lam * ε i b) / partitionFn q (ε i) lam by field_simp [(hq b).ne'],
    log_div (exp_pos _).ne' hZ.ne', log_exp]

/-- The log-odds score of a selected site is `-λ E(s)` up to the constant `∑ᵢ log Zᵢ`. -/
theorem score_logOdds_boltzmannPWM [Nonempty α] {q : α → ℝ} (hq : ∀ b, 0 < q b)
    (ε : Fin w → α → ℝ) (lam : ℝ) (s : Fin w → α) :
    score (logOdds (boltzmannPWM q ε lam) q) s =
      -lam * score ε s - ∑ i, log (partitionFn q (ε i) lam) := by
  simp only [score]
  rw [sum_congr rfl fun i _ => logOdds_boltzmannPWM hq ε lam i (s i), sum_sub_distrib, mul_sum]

/-! ## Motif-finding EM (OOPS and ZOOPS) -/

section EM

variable {n : ℕ} {Z : Type*} [Fintype Z] [DecidableEq α]

/-- The position `j + i` of motif column `i` for a motif starting at `j`, in a sequence of
length `n + w` (so `n + 1` possible starts). -/
def sitePos (j : Fin (n + 1)) (i : Fin w) : Fin (n + w) := ⟨j + i, by omega⟩

/-- The window of width `w` of `x` starting at `j`. -/
def window (x : Fin (n + w) → α) (j : Fin (n + 1)) : Fin w → α := fun i => x (sitePos j i)

/-- The likelihood ratio of the window at `j` under the site model `θ` against the background
`q`, and `1` when there is no motif occurrence. -/
noncomputable def windowRatio (q : α → ℝ) (θ : Fin w → α → ℝ) (x : Fin (n + w) → α) :
    Option (Fin (n + 1)) → ℝ
  | none => 1
  | some j => siteLik θ (window x j) / bgLik q (window x j)

/-- The joint likelihood of a sequence `x` and a latent occurrence `z` with prior `prior z` and
start `start z` (`none`: no occurrence): background letters outside the window, site-model letters
inside. One occurrence per sequence (OOPS) is `Z = Fin (n + 1)`, `start = some`, `prior` uniform;
zero or one (ZOOPS) is `Z = Option (Fin (n + 1))`, `start = id`, `prior none = 1 - γ` and
`prior (some j) = γ / (n + 1)` for a fixed `γ`. The background `q` is a fixed parameter. -/
noncomputable def motifJoint (q : α → ℝ) (prior : Z → ℝ) (start : Z → Option (Fin (n + 1)))
    (θ : Fin w → α → ℝ) (x : Fin (n + w) → α) (z : Z) : ℝ :=
  prior z * bgLik q x * windowRatio q θ x (start z)

omit [Fintype α] [Fintype Z] [DecidableEq α] in
/-- **The joint is the window model**: for a positive background and an occurrence at `j`, the
joint is the prior times the product of `θ (k - j)` inside the window and `q` outside. -/
theorem motifJoint_of_start_eq_some {q : α → ℝ} (hq : ∀ b, 0 < q b) (prior : Z → ℝ)
    (start : Z → Option (Fin (n + 1))) (θ : Fin w → α → ℝ) (x : Fin (n + w) → α) {z : Z}
    {j : Fin (n + 1)} (hz : start z = some j) :
    motifJoint q prior start θ x z = prior z * ∏ k : Fin (n + w),
      if h : (j : ℕ) ≤ k ∧ (k : ℕ) < j + w then θ ⟨k - j, by omega⟩ (x k) else q (x k) := by
  classical
  set F : Fin (n + w) → ℝ := fun k =>
    if h : (j : ℕ) ≤ k ∧ (k : ℕ) < j + w then θ ⟨k - j, by omega⟩ (x k) else q (x k) with hF
  set W := univ.image (sitePos (w := w) j) with hW
  have hinj : Set.InjOn (sitePos (w := w) j) (univ : Finset (Fin w)) := fun a _ b _ h => by
    simp only [sitePos, Fin.ext_iff] at h
    exact Fin.ext (by omega)
  have hmem : ∀ k : Fin (n + w), k ∈ W ↔ (j : ℕ) ≤ k ∧ (k : ℕ) < j + w := by
    intro k
    simp only [hW, mem_image, mem_univ, true_and, sitePos, Fin.ext_iff]
    constructor
    · rintro ⟨i, hi⟩; omega
    · intro h; exact ⟨⟨k - j, by omega⟩, by simp only; omega⟩
  have hA : bgLik q (window x j) = ∏ k ∈ W, q (x k) := by
    rw [hW, prod_image hinj]; rfl
  have hS : siteLik θ (window x j) = ∏ k ∈ W, F k := by
    rw [hW, prod_image hinj]
    refine prod_congr rfl fun i _ => ?_
    have hi : (j : ℕ) ≤ (sitePos j i : ℕ) ∧ (sitePos j i : ℕ) < j + w := by
      simp only [sitePos]; omega
    simp only [hF, dite_eq_left hi, window]
    congr 1
    exact Fin.ext (by simp [sitePos])
  have hB : ∏ k ∈ Wᶜ, F k = ∏ k ∈ Wᶜ, q (x k) := prod_congr rfl fun k hk => by
    simp only [hF]
    exact dite_eq_right fun h => (mem_compl.1 hk) ((hmem k).2 h)
  have hApos : 0 < ∏ k ∈ W, q (x k) := prod_pos fun k _ => hq _
  rw [motifJoint, hz, mul_assoc]
  congr 1
  simp only [windowRatio]
  rw [hA, hS, bgLik, ← prod_mul_prod_compl W (fun k => q (x k)), ← prod_mul_prod_compl W F, hB]
  field_simp

omit [Fintype α] [Fintype Z] [DecidableEq α] in
/-- With no occurrence, the joint is the prior times the background likelihood. -/
theorem motifJoint_of_start_eq_none (q : α → ℝ) (prior : Z → ℝ)
    (start : Z → Option (Fin (n + 1))) (θ : Fin w → α → ℝ) (x : Fin (n + w) → α) {z : Z}
    (hz : start z = none) : motifJoint q prior start θ x z = prior z * bgLik q x := by
  simp [motifJoint, hz, windowRatio]

/-- PWMs with positive entries and columns summing to `1`: the EM parameter space. -/
abbrev PosPWM (w : ℕ) (α : Type*) [Fintype α] : Type _ :=
  {θ : Fin w → α → ℝ // (∀ i b, 0 < θ i b) ∧ ∀ i, ∑ b, θ i b = 1}

/-- The motif model as an EM model on `PosPWM`. -/
noncomputable def motifModel (q : α → ℝ) (prior : Z → ℝ) (start : Z → Option (Fin (n + 1))) :
    PosPWM w α → (Fin (n + w) → α) → Z → ℝ :=
  fun θ => motifJoint q prior start θ.1

omit [Fintype Z] [DecidableEq α] in
/-- The motif model is positive for a positive background and a positive prior. -/
theorem motifModel_pos {q : α → ℝ} (hq : ∀ b, 0 < q b) {prior : Z → ℝ} (hprior : ∀ z, 0 < prior z)
    (start : Z → Option (Fin (n + 1))) (θ : PosPWM w α) (x : Fin (n + w) → α) (z : Z) :
    0 < motifModel q prior start θ x z := by
  have hθ := θ.2.1
  have hwr : 0 < windowRatio q θ.1 x (start z) := by
    cases start z with
    | none => simp [windowRatio]
    | some j =>
      exact div_pos (prod_pos fun i _ => hθ _ _) (prod_pos fun i _ => hq _)
  exact mul_pos (mul_pos (hprior z) (prod_pos fun k _ => hq _)) hwr

omit [DecidableEq α] in
/-- **The E-step in closed form**: the posterior of the occurrence `z` is proportional to its
prior times the likelihood ratio of its window (Lawrence and Reilly 1990; Bailey and Elkan
1995). -/
theorem posterior_motifModel {q : α → ℝ} (hq : ∀ b, 0 < q b) (prior : Z → ℝ)
    (start : Z → Option (Fin (n + 1))) (θ : PosPWM w α) (x : Fin (n + w) → α) (z : Z) :
    posterior (motifModel q prior start) θ x z =
      prior z * windowRatio q θ.1 x (start z) /
        ∑ z', prior z' * windowRatio q θ.1 x (start z') := by
  have hbg : 0 < bgLik q x := prod_pos fun k _ => hq _
  have hre : ∀ z', motifModel q prior start θ x z' =
      bgLik q x * (prior z' * windowRatio q θ.1 x (start z')) := fun z' => by
    simp only [motifModel, motifJoint]; ring
  rw [posterior, marginal, hre, sum_congr rfl fun z' _ => hre z', ← mul_sum,
    mul_div_mul_left _ _ hbg.ne']

variable {N : ℕ}

/-- The expected count of letter `b` in motif column `i` under the posteriors at `θ`:
`∑ₘ ∑_z P(z | xₘ, θ) [start z = some j ∧ xₘ (j + i) = b]`. -/
noncomputable def expectedCounts (q : α → ℝ) (prior : Z → ℝ) (start : Z → Option (Fin (n + 1)))
    (xs : Fin N → Fin (n + w) → α) (θ : PosPWM w α) (i : Fin w) (b : α) : ℝ :=
  ∑ m, ∑ z, posterior (motifModel q prior start) θ (xs m) z *
    (match start z with
      | none => 0
      | some j => if xs m (sitePos j i) = b then 1 else 0)

/-- Every letter can occur in every motif column: for each column `i` and letter `b` some
sequence has `b` at offset `i` of some possible occurrence. This keeps the M-step positive. -/
def Covers (start : Z → Option (Fin (n + 1))) (xs : Fin N → Fin (n + w) → α) : Prop :=
  ∀ (i : Fin w) (b : α), ∃ m z j, start z = some j ∧ xs m (sitePos j i) = b

/-- Under `Covers`, every expected count is positive. -/
theorem expectedCounts_pos [Nonempty Z] {q : α → ℝ} (hq : ∀ b, 0 < q b) {prior : Z → ℝ}
    (hprior : ∀ z, 0 < prior z) {start : Z → Option (Fin (n + 1))}
    {xs : Fin N → Fin (n + w) → α} (hcov : Covers start xs) (θ : PosPWM w α) (i : Fin w)
    (b : α) : 0 < expectedCounts q prior start xs θ i b := by
  obtain ⟨m, z, j, hz, hb⟩ := hcov i b
  have hpost : ∀ m z, 0 < posterior (motifModel q prior start) θ (xs m) z := fun m z =>
    div_pos (motifModel_pos hq hprior start θ _ z)
      (sum_pos (fun z' _ => motifModel_pos hq hprior start θ _ z') univ_nonempty)
  have hind : ∀ m z, 0 ≤ (match start z with
      | none => (0 : ℝ)
      | some j => if xs m (sitePos j i) = b then 1 else 0) := by
    intro m z
    split
    · exact le_rfl
    · split_ifs <;> norm_num
  refine sum_pos' (fun m _ => sum_nonneg fun z _ => mul_nonneg (hpost m z).le (hind m z))
    ⟨m, mem_univ _, sum_pos' (fun z _ => mul_nonneg (hpost m z).le (hind m z))
      ⟨z, mem_univ _, ?_⟩⟩
  rw [hz]
  simp only [hb, ite_true, mul_one]
  exact hpost m z

/-- The M-step: normalized expected letter counts, `θ' i b = c i b / ∑_{b'} c i b'`. -/
noncomputable def mStep [Nonempty α] [Nonempty Z] {q : α → ℝ} (hq : ∀ b, 0 < q b) {prior : Z → ℝ}
    (hprior : ∀ z, 0 < prior z) {start : Z → Option (Fin (n + 1))}
    {xs : Fin N → Fin (n + w) → α} (hcov : Covers start xs) (θ : PosPWM w α) : PosPWM w α :=
  ⟨fun i b => expectedCounts q prior start xs θ i b /
      ∑ b', expectedCounts q prior start xs θ i b',
    fun i b => div_pos (expectedCounts_pos hq hprior hcov θ i b)
      (Finset.sum_pos (fun b' _ => expectedCounts_pos hq hprior hcov θ i b')
        ⟨b, Finset.mem_univ b⟩),
    fun i => by
      rw [← Finset.sum_div, div_self (Finset.sum_pos
        (fun b' _ => expectedCounts_pos hq hprior hcov θ i b') ⟨Classical.arbitrary α,
          Finset.mem_univ _⟩).ne']⟩

/-- The letter indicator of motif column `i` for the occurrence `z` in `x`. -/
private noncomputable def occInd (start : Z → Option (Fin (n + 1))) (x : Fin (n + w) → α)
    (z : Z) (i : Fin w) (b : α) : ℝ :=
  match start z with
  | none => 0
  | some j => if x (sitePos j i) = b then 1 else 0

/-- The θ-independent part of the complete-data log-likelihood. -/
private noncomputable def logRest (q : α → ℝ) (prior : Z → ℝ)
    (start : Z → Option (Fin (n + 1))) (x : Fin (n + w) → α) (z : Z) : ℝ :=
  log (prior z) + log (bgLik q x) -
    match start z with
    | none => 0
    | some j => log (bgLik q (window x j))

omit [Fintype Z] in
private lemma log_motifModel {q : α → ℝ} (hq : ∀ b, 0 < q b) {prior : Z → ℝ}
    (hprior : ∀ z, 0 < prior z) (start : Z → Option (Fin (n + 1))) (θ : PosPWM w α)
    (x : Fin (n + w) → α) (z : Z) :
    log (motifModel q prior start θ x z) =
      logRest q prior start x z + ∑ i, ∑ b, occInd start x z i b * log (θ.1 i b) := by
  have hbg : ∀ {m : ℕ} (y : Fin m → α), 0 < bgLik q y := fun y => prod_pos fun k _ => hq _
  have hθ := θ.2.1
  have hwr : 0 < windowRatio q θ.1 x (start z) := by
    cases start z with
    | none => simp [windowRatio]
    | some j => exact div_pos (prod_pos fun i _ => hθ _ _) (hbg _)
  simp only [motifModel, motifJoint, logRest, occInd]
  rw [log_mul (mul_pos (hprior z) (hbg x)).ne' hwr.ne', log_mul (hprior z).ne' (hbg x).ne']
  revert hwr
  cases start z with
  | none => intro _; simp [windowRatio]
  | some j =>
    intro _
    have hsl : 0 < siteLik θ.1 (window x j) := prod_pos fun i _ => hθ _ _
    simp only [windowRatio]
    rw [log_div hsl.ne' (hbg _).ne', siteLik,
      log_prod fun i _ => (hθ _ _).ne']
    simp only [ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, ite_true, window]
    ring

private lemma emQ_motifModel_eq {q : α → ℝ} (hq : ∀ b, 0 < q b) {prior : Z → ℝ}
    (hprior : ∀ z, 0 < prior z) (start : Z → Option (Fin (n + 1)))
    (xs : Fin N → Fin (n + w) → α) (θ θ' : PosPWM w α) :
    emQ (motifModel q prior start) xs θ' θ =
      (∑ m, ∑ z, posterior (motifModel q prior start) θ (xs m) z *
        logRest q prior start (xs m) z) +
      ∑ i, ∑ b, expectedCounts q prior start xs θ i b * log (θ'.1 i b) := by
  simp only [emQ, log_motifModel hq hprior, mul_add, sum_add_distrib]
  congr 1
  simp only [expectedCounts, mul_sum, sum_mul, mul_assoc]
  change ∑ m, ∑ z, ∑ i, ∑ b, posterior (motifModel q prior start) θ (xs m) z *
      (occInd start (xs m) z i b * log (θ'.1 i b)) =
    ∑ i, ∑ b, ∑ m, ∑ z, posterior (motifModel q prior start) θ (xs m) z *
      (occInd start (xs m) z i b * log (θ'.1 i b))
  calc _ = ∑ m, ∑ i, ∑ z, ∑ b, posterior (motifModel q prior start) θ (xs m) z *
        (occInd start (xs m) z i b * log (θ'.1 i b)) := sum_congr rfl fun m _ => sum_comm
    _ = ∑ m, ∑ i, ∑ b, ∑ z, posterior (motifModel q prior start) θ (xs m) z *
        (occInd start (xs m) z i b * log (θ'.1 i b)) :=
          sum_congr rfl fun m _ => sum_congr rfl fun i _ => sum_comm
    _ = ∑ i, ∑ m, ∑ b, ∑ z, posterior (motifModel q prior start) θ (xs m) z *
        (occInd start (xs m) z i b * log (θ'.1 i b)) := sum_comm
    _ = _ := sum_congr rfl fun i _ => sum_comm

/-- **The M-step maximizes the EM objective** over PWMs with positive entries and normalized
columns: for every `θ'`, `Q(θ' | θ) ≤ Q(mStep θ | θ)` (Gibbs' inequality per column). -/
theorem emQ_le_emQ_mStep [Nonempty α] [Nonempty Z] {q : α → ℝ} (hq : ∀ b, 0 < q b) {prior : Z → ℝ}
    (hprior : ∀ z, 0 < prior z) {start : Z → Option (Fin (n + 1))} {xs : Fin N → Fin (n + w) → α}
    (hcov : Covers start xs) (θ θ' : PosPWM w α) :
    emQ (motifModel q prior start) xs θ' θ ≤
      emQ (motifModel q prior start) xs (mStep hq hprior hcov θ) θ := by
  rw [emQ_motifModel_eq hq hprior, emQ_motifModel_eq hq hprior]
  apply add_le_add_right
  refine sum_le_sum fun i _ => ?_
  have hc := expectedCounts_pos hq hprior hcov θ i
  exact Cslib.MachineLearning.LatentVariable.BernoulliMixture.sum_mul_log_le_sum_mul_log_div
    (fun b => (hc b).le) (sum_pos (fun b _ => hc b) univ_nonempty) (θ'.2.1 i) (θ'.2.2 i)

/-- **The motif likelihood is nondecreasing along the EM iterates.** -/
theorem logLik_iterate_mStep_monotone [Nonempty α] [Nonempty Z] {q : α → ℝ} (hq : ∀ b, 0 < q b)
    {prior : Z → ℝ} (hprior : ∀ z, 0 < prior z) {start : Z → Option (Fin (n + 1))}
    {xs : Fin N → Fin (n + w) → α} (hcov : Covers start xs) (θ₀ : PosPWM w α) :
    Monotone fun k => logLik (motifModel q prior start) xs ((mStep hq hprior hcov)^[k] θ₀) := by
  exact logLik_iterate_monotone (fun θ x z => motifModel_pos hq hprior start θ x z) xs
    (fun θ => emQ_le_emQ_mStep hq hprior hcov θ θ) θ₀

end EM

/-! ## The Karlin–Altschul `λ` -/

/-- The moment generating function `∑ₐ ∑_b pₐ p_b e^{λ s_{ab}}` of a pair score under independent
letters with law `p`. -/
noncomputable def pairMGF (p : α → ℝ) (s : α → α → ℝ) (lam : ℝ) : ℝ :=
  ∑ a, ∑ b, p a * p b * exp (lam * s a b)

private lemma pairMGF_zero {p : α → ℝ} (hp : IsDist p) (s : α → α → ℝ) :
    pairMGF p s 0 = 1 := by
  simp only [pairMGF, zero_mul, exp_zero, mul_one, ← mul_sum, hp.2]

private lemma continuous_pairMGF (p : α → ℝ) (s : α → α → ℝ) : Continuous (pairMGF p s) := by
  unfold pairMGF
  fun_prop

/-- The chord inequality of the strictly convex `pairMGF` on the segment from `0` to `l`. -/
private lemma pairMGF_chord {p : α → ℝ} (hp0 : ∀ a, 0 < p a) {s : α → α → ℝ}
    (hne : ∃ a b, s a b ≠ 0) {t l : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hl : l ≠ 0) :
    pairMGF p s (t * l) < (1 - t) * pairMGF p s 0 + t * pairMGF p s l := by
  obtain ⟨a₀, b₀, hs⟩ := hne
  have hrhs : (1 - t) * pairMGF p s 0 + t * pairMGF p s l =
      ∑ a, ∑ b, p a * p b * ((1 - t) * exp (0 * s a b) + t * exp (l * s a b)) := by
    simp only [pairMGF, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    ring
  have hterm : ∀ a b, exp (t * l * s a b) ≤ (1 - t) * exp (0 * s a b) + t * exp (l * s a b) :=
    fun a b => by
      have := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ (l * s a b))
        (sub_pos.2 ht1).le ht0.le (by ring)
      simp only [smul_eq_mul, mul_zero, zero_add] at this
      rw [zero_mul]
      calc exp (t * l * s a b) = exp (t * (l * s a b)) := by ring_nf
        _ ≤ _ := this
  have hstrict : exp (t * l * s a₀ b₀) <
      (1 - t) * exp (0 * s a₀ b₀) + t * exp (l * s a₀ b₀) := by
    have := strictConvexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ (l * s a₀ b₀))
      (mul_ne_zero hl hs).symm (sub_pos.2 ht1) ht0 (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add] at this
    rw [zero_mul]
    calc exp (t * l * s a₀ b₀) = exp (t * (l * s a₀ b₀)) := by ring_nf
      _ < _ := this
  rw [hrhs, pairMGF]
  have hpp : ∀ a b, 0 < p a * p b := fun a b => mul_pos (hp0 a) (hp0 b)
  refine sum_lt_sum (fun a _ => sum_le_sum fun b _ =>
    mul_le_mul_of_nonneg_left (hterm a b) (hpp a b).le) ⟨a₀, mem_univ _, ?_⟩
  exact sum_lt_sum (fun b _ => mul_le_mul_of_nonneg_left (hterm a₀ b) (hpp a₀ b).le)
    ⟨b₀, mem_univ _, mul_lt_mul_of_pos_left hstrict (hpp a₀ b₀)⟩

/-- Below a positive root `l` of `pairMGF = 1`, `pairMGF < 1`. -/
private lemma pairMGF_lt_one {p : α → ℝ} (hp : IsDist p) (hp0 : ∀ a, 0 < p a)
    {s : α → α → ℝ} (hne : ∃ a b, s a b ≠ 0) {l₁ l₂ : ℝ} (h1 : 0 < l₁) (h12 : l₁ < l₂)
    (h2 : pairMGF p s l₂ = 1) : pairMGF p s l₁ < 1 := by
  have hl2 : 0 < l₂ := h1.trans h12
  have h := pairMGF_chord hp0 hne (t := l₁ / l₂) (div_pos h1 hl2)
    ((div_lt_one hl2).2 h12) hl2.ne'
  rwa [div_mul_cancel₀ _ hl2.ne', pairMGF_zero hp, h2, mul_one, mul_one, sub_add_cancel] at h

/-- **Karlin–Altschul `λ`** (Karlin and Altschul 1990): if the expected score under a positive
background distribution is negative and some score is positive, there is a unique `λ > 0` with
`∑ pₐ p_b e^{λ s_{ab}} = 1`. -/
theorem existsUnique_pairMGF_eq_one {p : α → ℝ} {s : α → α → ℝ} (hp : IsDist p)
    (hp0 : ∀ a, 0 < p a) (hneg : ∑ a, ∑ b, p a * p b * s a b < 0) (hpos : ∃ a b, 0 < s a b) :
    ∃! lam, 0 < lam ∧ pairMGF p s lam = 1 := by
  obtain ⟨a₀, b₀, hs⟩ := hpos
  have hne : ∃ a b, s a b ≠ 0 := ⟨a₀, b₀, hs.ne'⟩
  -- a small `l₀ > 0` with `pairMGF < 1`, from the negative slope at `0`
  have hd : HasDerivAt (pairMGF p s) (∑ a, ∑ b, p a * p b * s a b) 0 := by
    have h := HasDerivAt.sum (u := univ) (x := (0 : ℝ)) fun a _ => HasDerivAt.sum (u := univ)
      fun b _ => (((hasDerivAt_id (0 : ℝ)).mul_const (s a b)).exp).const_mul (p a * p b)
    convert h using 1
    · ext l; simp [pairMGF]
    · simp
  have hsl := (hasDerivAt_iff_tendsto_slope.1 hd).mono_left
    (nhdsWithin_mono (0 : ℝ) (show Set.Ioi (0 : ℝ) ⊆ {0}ᶜ from fun x hx => (Set.mem_Ioi.1 hx).ne'))
  obtain ⟨l₀, hl₀neg, hl₀pos⟩ :=
    ((hsl.eventually (gt_mem_nhds hneg)).and self_mem_nhdsWithin).exists
  have hl₀pos' : (0 : ℝ) < l₀ := hl₀pos
  have hf₀ : pairMGF p s l₀ < 1 := by
    rw [slope_def_field, pairMGF_zero hp, sub_zero] at hl₀neg
    have := (div_neg_iff.1 hl₀neg)
    rcases this with ⟨_, h⟩ | ⟨h, _⟩
    · linarith
    · linarith
  -- a large `L > 0` with `pairMGF > 1`, from the positive score
  set c := p a₀ * p b₀ with hc
  have hc0 : 0 < c := mul_pos (hp0 a₀) (hp0 b₀)
  set L := (|log c| + 1) / s a₀ b₀ with hL
  have hLpos : 0 < L := div_pos (by positivity) hs
  have hfL : 1 < pairMGF p s L := by
    have hterm : c * exp (L * s a₀ b₀) ≤ pairMGF p s L := by
      have hnn : ∀ a b, 0 ≤ p a * p b * exp (L * s a b) := fun a b =>
        mul_nonneg (mul_pos (hp0 a) (hp0 b)).le (exp_pos _).le
      calc c * exp (L * s a₀ b₀) ≤ ∑ b, p a₀ * p b * exp (L * s a₀ b) :=
            single_le_sum (f := fun b => p a₀ * p b * exp (L * s a₀ b))
              (fun b _ => hnn a₀ b) (mem_univ b₀)
        _ ≤ pairMGF p s L :=
            single_le_sum (f := fun a => ∑ b, p a * p b * exp (L * s a b))
              (fun a _ => sum_nonneg fun b _ => hnn a b) (mem_univ a₀)
    have hexp : c⁻¹ < exp (L * s a₀ b₀) := by
      rw [hL, div_mul_cancel₀ _ hs.ne', ← exp_log (inv_pos.2 hc0)]
      exact exp_lt_exp.2 (by rw [log_inv]; linarith [neg_le_abs (log c)])
    have := mul_lt_mul_of_pos_left hexp hc0
    rw [mul_inv_cancel₀ hc0.ne'] at this
    linarith
  -- existence by the intermediate value theorem, uniqueness by strict convexity
  obtain ⟨l, hl, hfl⟩ := intermediate_value_uIcc (continuous_pairMGF p s).continuousOn
    (Set.mem_uIcc.2 (Or.inl ⟨hf₀.le, hfL.le⟩))
  have hlpos : 0 < l := lt_of_lt_of_le (lt_min hl₀pos' hLpos) (Set.mem_uIcc.1 hl |>.elim
    (fun h => le_trans (min_le_left _ _) h.1) (fun h => le_trans (min_le_right _ _) h.1))
  refine ⟨l, ⟨hlpos, hfl⟩, fun μ ⟨hμ, hfμ⟩ => ?_⟩
  rcases lt_trichotomy μ l with h | h | h
  · exact absurd hfμ (pairMGF_lt_one hp hp0 hne hμ h hfl).ne
  · exact h
  · exact absurd hfl (pairMGF_lt_one hp hp0 hne hlpos h hfμ).ne

/-- The implicit target frequencies `q_{ab} = pₐ p_b e^{λ s_{ab}}` of a score matrix. -/
noncomputable def targetFreq (p : α → ℝ) (s : α → α → ℝ) (lam : ℝ) (ab : α × α) : ℝ :=
  p ab.1 * p ab.2 * exp (lam * s ab.1 ab.2)

/-- At a root of `pairMGF p s λ = 1` the target frequencies form a distribution on pairs. -/
theorem isDist_targetFreq {p : α → ℝ} {s : α → α → ℝ} (hp0 : ∀ a, 0 < p a) {lam : ℝ}
    (hlam : pairMGF p s lam = 1) : IsDist (targetFreq p s lam) := by
  refine ⟨fun ab => (mul_pos (mul_pos (hp0 _) (hp0 _)) (exp_pos _)).le, ?_⟩
  rw [Fintype.sum_prod_type]
  exact hlam

omit [Fintype α] in
/-- **Every such score matrix is a log-odds matrix** (Karlin and Altschul 1990):
`s_{ab} = log (q_{ab} / (pₐ p_b)) / λ` for every `λ > 0`; at the Karlin–Altschul root the
`q_{ab}` form a distribution (`isDist_targetFreq`), the implicit target frequencies. -/
theorem score_eq_log_targetFreq {p : α → ℝ} (hp0 : ∀ a, 0 < p a) (s : α → α → ℝ) {lam : ℝ}
    (hlam : 0 < lam) (a b : α) : s a b = log (targetFreq p s lam (a, b) / (p a * p b)) / lam := by
  simp only [targetFreq]
  rw [mul_div_cancel_left₀ _ (mul_pos (hp0 a) (hp0 b)).ne', log_exp,
    mul_div_cancel_left₀ _ hlam.ne']

/-- **The relative entropy of the target frequencies** (Altschul 1991):
`λ ∑ q_{ab} s_{ab} = ∑ q_{ab} log (q_{ab} / (pₐ p_b))`, which is nonnegative. -/
theorem relEntropy_eq_and_nonneg {p : α → ℝ} {s : α → α → ℝ} (hp : IsDist p)
    (hp0 : ∀ a, 0 < p a) {lam : ℝ} (hlam : pairMGF p s lam = 1) :
    lam * ∑ ab, targetFreq p s lam ab * s ab.1 ab.2 =
        ∑ ab, targetFreq p s lam ab * log (targetFreq p s lam ab / (p ab.1 * p ab.2)) ∧
      0 ≤ lam * ∑ ab, targetFreq p s lam ab * s ab.1 ab.2 := by
  have hpp : ∀ ab : α × α, 0 < p ab.1 * p ab.2 := fun ab => mul_pos (hp0 _) (hp0 _)
  have hq : ∀ ab, 0 < targetFreq p s lam ab := fun ab => mul_pos (hpp ab) (exp_pos _)
  have hterm : ∀ ab : α × α, targetFreq p s lam ab *
      log (targetFreq p s lam ab / (p ab.1 * p ab.2)) =
        lam * (targetFreq p s lam ab * s ab.1 ab.2) := by
    intro ab
    simp only [targetFreq]
    rw [mul_div_cancel_left₀ _ (hpp ab).ne', log_exp]
    ring
  have heq : lam * ∑ ab, targetFreq p s lam ab * s ab.1 ab.2 =
      ∑ ab, targetFreq p s lam ab * log (targetFreq p s lam ab / (p ab.1 * p ab.2)) := by
    rw [mul_sum]
    exact sum_congr rfl fun ab _ => (hterm ab).symm
  refine ⟨heq, ?_⟩
  rw [heq]
  have hsum : ∑ ab : α × α, p ab.1 * p ab.2 = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [← mul_sum, ← sum_mul, hp.2, one_mul]
  have h := sum_mul_log_sub_le hpp (isDist_targetFreq hp0 hlam)
  rw [hsum, log_one] at h
  have hterm' : ∀ ab, targetFreq p s lam ab * log (targetFreq p s lam ab / (p ab.1 * p ab.2)) =
      -(targetFreq p s lam ab * (log (p ab.1 * p ab.2) - log (targetFreq p s lam ab))) := by
    intro ab
    rw [log_div (hq ab).ne' (hpp ab).ne']
    ring
  simp only [hterm', sum_neg_distrib]
  linarith

/-- **The target score is positive**: at the Karlin–Altschul root `λ > 0`, the expected score
`∑ q_{ab} s_{ab}` under the target frequencies is positive. -/
theorem sum_targetFreq_mul_pos {p : α → ℝ} {s : α → α → ℝ} (hp : IsDist p)
    (hp0 : ∀ a, 0 < p a) (hpos : ∃ a b, 0 < s a b) {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : pairMGF p s lam = 1) : 0 < ∑ ab, targetFreq p s lam ab * s ab.1 ab.2 := by
  obtain ⟨a₀, b₀, hs⟩ := hpos
  have hne : ∃ a b, s a b ≠ 0 := ⟨a₀, b₀, hs.ne'⟩
  have hhalf : pairMGF p s (lam / 2) < 1 :=
    pairMGF_lt_one hp hp0 hne (half_pos hlam0) (half_lt_self hlam0) hlam
  -- termwise `exp y - exp x ≤ (y - x) exp y`
  have hterm : ∀ a b, p a * p b * exp (lam * s a b) - p a * p b * exp (lam / 2 * s a b) ≤
      lam / 2 * (p a * p b * exp (lam * s a b) * s a b) := by
    intro a b
    have h1 := add_one_le_exp (lam / 2 * s a b - lam * s a b)
    have h2 : exp (lam / 2 * s a b) = exp (lam * s a b) * exp (lam / 2 * s a b - lam * s a b) :=
      by rw [← exp_add]; ring_nf
    have hpp : 0 ≤ p a * p b := (mul_pos (hp0 a) (hp0 b)).le
    rw [h2]
    have := mul_le_mul_of_nonneg_left h1 (mul_nonneg hpp (exp_pos (lam * s a b)).le)
    nlinarith
  have hsum : pairMGF p s lam - pairMGF p s (lam / 2) ≤
      lam / 2 * ∑ ab, targetFreq p s lam ab * s ab.1 ab.2 := by
    rw [Fintype.sum_prod_type, mul_sum, pairMGF, pairMGF, ← sum_sub_distrib]
    refine sum_le_sum fun a _ => ?_
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_le_sum fun b _ => hterm a b
  rw [hlam] at hsum
  by_contra hle
  replace hle := not_lt.1 hle
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (half_pos hlam0).le hle]

end Cslib.Bioinformatics.Motifs.PWM

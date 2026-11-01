/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Phylogenetics.FelsensteinPruning
public import MathlibExt.Probability.Statistics.NeymanPearson
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# PhyloCSF as a phylogenetic likelihood-ratio classifier

PhyloCSF (Lin, Jungreis and Kellis 2011) decides whether an alignment of codons is protein
coding by comparing two phylogenetic models on the same tree: an empirical codon model fit to
coding regions and one fit to non-coding regions. The score is the log-likelihood ratio of the
alignment under the two models, and the alignment is called coding when the score exceeds a
cutoff.

We model the two hypotheses as two pruning trees `tC`, `tN` (`FelsensteinPruning.Tree`, with the
transition matrices of the coding and the non-coding model on every branch) and two root
distributions `πC`, `πN`, on the state space `S` of codons. The codon columns of an alignment
`A : Fin m → L → S` evolve independently, so its likelihood is the product of the site
likelihoods, each computed by pruning (`alignLik`).

## Main results

* `score_eq_log_div`: the PhyloCSF score `∑ k, log (L_C(A k) / L_N(A k))` is the log of the
  likelihood ratio of the whole alignment.
* `siteLik_eq_sum_prune`: each site likelihood is computed by Felsenstein's pruning.
* `weighted_power_le_scoreTest`: **the score threshold test is most powerful for
  unnormalized weights** (the dominated Neyman–Pearson inequality on the finite set of
  alignments): no test whose weighted size under the non-coding weights is at most that of
  the threshold test has larger weighted power under the coding weights. The hypotheses
  assume only positivity of the site likelihoods, not that either pruning model defines a
  probability distribution, so the sums need not be probabilities; genuine statistical
  size and power for two simple hypotheses would additionally need normalization
  (`∑ A, alignLik = 1` for each model).

The optimality is for fixed model parameters (two simple hypotheses). As published, PhyloCSF
also fits a scale factor for the branch lengths of each model by maximum likelihood on each
alignment; the statistic is then a generalized likelihood ratio, and the Neyman–Pearson
optimality proved here does not cover it.

## References

* M. F. Lin, I. Jungreis, M. Kellis, *PhyloCSF: a comparative genomics method to distinguish
  protein coding and non-coding regions*, Bioinformatics 27 (2011), i275–i282.
* J. Neyman and E. S. Pearson, *On the problem of the most efficient tests of statistical
  hypotheses*, Phil. Trans. R. Soc. Lond. A 231 (1933), 289–337.
-/

@[expose] public section

namespace Cslib.Bioinformatics.Phylogenetics.PhyloCSF

open Finset MeasureTheory
open Real (log exp log_prod exp_pos lt_log_iff_exp_lt)
open Cslib.Bioinformatics.Phylogenetics.FelsensteinPruning

variable {L S : Type*} [Fintype S] [DecidableEq S] {m : ℕ}

/-- The leaf data of an alignment column `col : L → S`: the indicator of the observed codon at
each leaf. -/
def leafData (col : L → S) (l : L) (s : S) : ℝ := if col l = s then 1 else 0

/-- The likelihood of one alignment column under the model `(t, π)`. -/
noncomputable def siteLik (t : Tree L S ℝ) (π : S → ℝ) (col : L → S) : ℝ :=
  likelihood (leafData col) t π

/-- The likelihood of an alignment of `m` independent columns: the product of the site
likelihoods. -/
noncomputable def alignLik (t : Tree L S ℝ) (π : S → ℝ) (A : Fin m → L → S) : ℝ :=
  ∏ k, siteLik t π (A k)

/-- **The PhyloCSF score**: the sum over the columns of the log-likelihood ratio of the coding
model `(tC, πC)` against the non-coding model `(tN, πN)`. -/
noncomputable def score (tC : Tree L S ℝ) (πC : S → ℝ) (tN : Tree L S ℝ) (πN : S → ℝ)
    (A : Fin m → L → S) : ℝ :=
  ∑ k, log (siteLik tC πC (A k) / siteLik tN πN (A k))

/-- Each site likelihood is computed by Felsenstein's pruning algorithm. -/
theorem siteLik_eq_sum_prune (t : Tree L S ℝ) (π : S → ℝ) (col : L → S) :
    siteLik t π col = ∑ s, π s * prune (leafData col) t s :=
  likelihood_eq_sum_prune _ t π

/-- **The score is the log-likelihood ratio of the alignment** when all site likelihoods are
positive. -/
theorem score_eq_log_div {tC tN : Tree L S ℝ} {πC πN : S → ℝ} {A : Fin m → L → S}
    (hC : ∀ k, 0 < siteLik tC πC (A k)) (hN : ∀ k, 0 < siteLik tN πN (A k)) :
    score tC πC tN πN A = log (alignLik tC πC A / alignLik tN πN A) := by
  rw [alignLik, alignLik, ← prod_div_distrib, log_prod fun k _ => (div_pos (hC k) (hN k)).ne',
    score]

/-- The threshold test on the score: call the alignment coding (`1`) iff the score exceeds the
cutoff `c`. -/
noncomputable def scoreTest (tC : Tree L S ℝ) (πC : S → ℝ) (tN : Tree L S ℝ) (πN : S → ℝ)
    (c : ℝ) (A : Fin m → L → S) : Set.Icc (0 : ℝ) 1 :=
  if c < score tC πC tN πN A then ⟨1, by norm_num, le_rfl⟩ else ⟨0, le_rfl, by norm_num⟩

variable [Fintype L] [DecidableEq L]

/-- **PhyloCSF's score threshold test is most powerful for unnormalized weights**: with
positive site likelihoods under both models, a randomized test `φ` whose weighted size under
the non-coding weights is at most that of `scoreTest c` has at most its weighted power under
the coding weights. This is the dominated Neyman–Pearson inequality for the unnormalized
alignment weights `alignLik`; it becomes a statement about statistical size and power only
under additional normalization hypotheses (`∑ A, alignLik = 1` for each model). -/
theorem weighted_power_le_scoreTest {tC tN : Tree L S ℝ} {πC πN : S → ℝ}
    (hC : ∀ col, 0 < siteLik tC πC col) (hN : ∀ col, 0 < siteLik tN πN col) (c : ℝ)
    (φ : (Fin m → L → S) → Set.Icc (0 : ℝ) 1)
    (hsize : ∑ A, (φ A).val * alignLik tN πN A ≤
      ∑ A : Fin m → L → S, (scoreTest tC πC tN πN c A).val * alignLik tN πN A) :
    ∑ A, (φ A).val * alignLik tC πC A ≤
      ∑ A : Fin m → L → S, (scoreTest tC πC tN πN c A).val * alignLik tC πC A := by
  let _ : MeasurableSpace (Fin m → L → S) := ⊤
  have hdisc : DiscreteMeasurableSpace (Fin m → L → S) := ⟨fun _ => trivial⟩
  have hNpos : ∀ A : Fin m → L → S, 0 < alignLik tN πN A := fun A => prod_pos fun k _ => hN (A k)
  have hCpos : ∀ A : Fin m → L → S, 0 < alignLik tC πC A := fun A => prod_pos fun k _ => hC (A k)
  have hiff : ∀ A : Fin m → L → S,
      c < score tC πC tN πN A ↔ exp c * alignLik tN πN A < alignLik tC πC A := by
    intro A
    rw [score_eq_log_div (fun k => hC _) (fun k => hN _), lt_log_iff_exp_lt
      (div_pos (hCpos A) (hNpos A)), lt_div_iff₀ (hNpos A)]
  have hint : ∀ f : (Fin m → L → S) → ℝ, ∫ A, f A ∂Measure.count = ∑ A, f A := fun f => by
    simp [integral_fintype]
  have key := MathlibExt.Probability.Statistics.NeymanPearson.neyman_pearson_dominated_two_simple
    (μ := Measure.count) (p := alignLik tN πN) (q := alignLik tC πC)
    (measurable_of_countable _) (measurable_of_countable _) (fun A => (hNpos A).le)
    (fun A => (hCpos A).le) (Integrable.of_finite) (Integrable.of_finite) (exp c)
    (exp_pos c).le (scoreTest tC πC tN πN c) (measurable_of_countable _)
    (fun A h => by simp [scoreTest, (hiff A).2 h])
    (fun A h => by simp [scoreTest, (hiff A).not.2 (not_lt.2 h.le)])
    φ (measurable_of_countable _)
  have h := key (by simpa only [hint] using hsize)
  simpa only [hint] using h

end Cslib.Bioinformatics.Phylogenetics.PhyloCSF

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.Statistics.MultipleTesting.Knockoff
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# False discovery rate control by the knockoff filter

The knockoff filter of R. F. Barber and E. J. Candès (*Controlling the false discovery rate via
knockoffs*, Ann. Statist. 43 (2015), arXiv:1404.5609) and its model-X form (E. Candès, Y. Fan,
L. Janson and J. Lv, *Panning for gold*, J. R. Statist. Soc. B 80 (2018), arXiv:1610.02351)
controls the false discovery rate in finite samples. Both proofs have two parts: a construction
(fixed-design knockoffs for the Gaussian linear model, or model-X knockoffs with
`(X, X̃)_swap(S) =ᵈ (X, X̃)` and `X̃ ⊥ Y | X`) that makes the signs of the null statistics `W_j`
i.i.d. fair coins independent of `|W|` (Barber–Candès Lemma 1; Candès et al. Lemma 3.3), and a
probabilistic argument showing that any statistics with that sign property give FDR control
(Barber–Candès Theorems 1-2; Candès et al. Theorem 3.4, whose proof "is the same as that of
Theorems 1 and 2 in [Barber–Candès], since all we need is that the null statistics have signs
distributed as i.i.d. coin flips"). The statements below are the second part, with the sign
property written as invariance of the law of `W` under flipping the signs of any set of null
statistics (`flipSigns`), which is how both lemmas are proved. Their proofs (a supermartingale
and optional-stopping argument) are deferred.
-/

@[expose] public section

open MeasureTheory
open MathlibExt.Probability.Statistics.MultipleTesting
open MathlibExt.Probability.Statistics.MultipleTesting.Knockoff

namespace MathlibExt.Probability.KnockoffFDRWanted

/-- **FDR control by knockoff+.** Let `W : Ω → ℝ^p` be measurable statistics on a probability
space and `H0` the set of null variables, and suppose that flipping the signs of any set `S ⊆ H0`
of null statistics leaves the law of `W` unchanged. Then for `0 ≤ q ≤ 1` the knockoff+ selection
`Ŝ = {j : W_j ≥ T₊}` has false discovery rate `E[|Ŝ ∩ H0| / (|Ŝ| ∨ 1)] ≤ q`.

Source: R. F. Barber and E. J. Candès, *Controlling the false discovery rate via knockoffs*,
Ann. Statist. 43 (2015) 2055-2085, arXiv:1404.5609, Theorem 2, through Lemma 1 (i.i.d. signs for
the nulls), which is the only property of `W` its proof uses; E. Candès, Y. Fan, L. Janson and
J. Lv, *Panning for gold: model-X knockoffs for high dimensional controlled variable selection*,
J. R. Statist. Soc. B 80 (2018), arXiv:1610.02351, Theorem 3.4 (knockoff+ part) with Lemma 3.3. -/
theorem_wanted integral_falseDiscoveryProportion_knockoffSelection_one_le {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {p : ℕ} {W : Ω → Fin p → ℝ}
    (hW : Measurable W) (H0 : Finset (Fin p))
    (hflip : ∀ S ⊆ H0, μ.map (fun ω => flipSigns S (W ω)) = μ.map W) {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) :
    ∫ ω, falseDiscoveryProportion H0 (knockoffSelection 1 q (W ω)) ∂μ ≤ q

/-- **Modified FDR control by knockoff.** Under the hypotheses of
`integral_falseDiscoveryProportion_knockoffSelection_one_le`, for `0 < q ≤ 1` the knockoff
selection `Ŝ = {j : W_j ≥ T}` (offset `0`) satisfies `E[|Ŝ ∩ H0| / (|Ŝ| + q⁻¹)] ≤ q`.

Source: R. F. Barber and E. J. Candès, *Controlling the false discovery rate via knockoffs*,
Ann. Statist. 43 (2015), arXiv:1404.5609, Theorem 1 (stated for `q ∈ [0, 1]`; at `q = 0` the
selection is empty and the bound is trivial, so only `0 < q` is kept here), through Lemma 1;
E. Candès, Y. Fan, L. Janson and J. Lv, J. R. Statist. Soc. B 80 (2018), arXiv:1610.02351,
Theorem 3.4 (knockoff part) with Lemma 3.3. -/
theorem_wanted integral_card_inter_div_knockoffSelection_zero_le {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {p : ℕ} {W : Ω → Fin p → ℝ}
    (hW : Measurable W) (H0 : Finset (Fin p))
    (hflip : ∀ S ⊆ H0, μ.map (fun ω => flipSigns S (W ω)) = μ.map W) {q : ℝ} (hq0 : 0 < q)
    (hq1 : q ≤ 1) :
    ∫ ω, ((knockoffSelection 0 q (W ω) ∩ H0).card : ℝ) /
        ((knockoffSelection 0 q (W ω)).card + q⁻¹) ∂μ ≤ q

end MathlibExt.Probability.KnockoffFDRWanted

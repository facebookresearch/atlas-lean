/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Case-only odds ratios and multiplicative interaction

For binary genotype $G$, exposure $E$ and disease $D$, the positive case and non-case cell
masses are $(a,b)$, $(c,d)$, $(e,f)$ and $(g,h)$ in strata $(G,E) = (0,0), (1,0), (0,1), (1,1)$,
respectively. If $G$ and $E$ are independent among non-cases, equivalently $bh = df$, the
multiplicative odds-ratio interaction equals the case-only odds ratio $ag/(ce)$. The identity
uses neither population independence nor a rare-disease approximation. Counts and normalized
masses give the same ratios, so no normalization hypothesis is needed.

A second result gives a positive table with dependence among non-cases and in the population,
with both multiplicative interactions equal to $1$ but the case-only odds ratio different from $1$.

## References

* Tyler J. VanderWeele, Sonia Hernández-Díaz and Miguel A. Hernán,
  *Case-only gene-environment interaction studies: when does association imply mechanistic
  interaction?*, Genetic Epidemiology 34 (2010), 327–334, Table 1 and Appendix A
  (Independence Assumption of the Case-Only Study).
  <https://pmc.ncbi.nlm.nih.gov/articles/PMC3112477/>
* Walter W. Piegorsch, Clarice R. Weinberg and Jack A. Taylor,
  *Non-hierarchical logistic models and case-only designs for assessing susceptibility in
  population-based case-control studies*, Statistics in Medicine 13 (1994), 153–162,
  the odds-ratio derivation credited in Appendix A of the preceding paper.
  <https://pubmed.ncbi.nlm.nih.gov/8122051/>
-/

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.CaseOnlyInteractionWanted

/-- The risk-ratio interaction `SRR = RR_ge / (RR_g RR_e)` for cell masses `a, …, h` (cases and
non-cases at `(G, E) = (0, 0), (1, 0), (0, 1), (1, 1)`), where each relative risk compares the risk
in a cell with the risk `a / (a + b)` in the doubly unexposed cell. It is meaningful for positive
cell masses; if any denominator is `0`, Lean's convention `x / 0 = 0` applies. -/
noncomputable def riskRatioInteraction (a b c d e f g h : ℝ) : ℝ :=
  (g / (g + h) / (a / (a + b))) /
    ((c / (c + d) / (a / (a + b))) * (e / (e + f) / (a / (a + b))))

/-- The odds-ratio interaction `SOR = OR_ge / (OR_g OR_e)`, with `OR_g = b c / (a d)`,
`OR_e = b e / (a f)` and `OR_ge = b g / (a h)`. It is meaningful for positive cell masses; if any
denominator is `0`, Lean's convention `x / 0 = 0` applies. -/
noncomputable def oddsRatioInteraction (a b c d e f g h : ℝ) : ℝ :=
  (b * g / (a * h)) / ((b * c / (a * d)) * (b * e / (a * f)))

/-- The case-only odds ratio `a g / (c e)` between genotype and exposure among the cases. It is
meaningful when `c e ≠ 0`; if `c e = 0`, Lean's convention `x / 0 = 0` makes the value `0`. -/
noncomputable def caseOnlyOddsRatio (a c e g : ℝ) : ℝ :=
  a * g / (c * e)

/-- **Case-only odds ratio under non-case independence** (Piegorsch, Weinberg and Taylor 1994;
VanderWeele et al. 2010, Appendix A). Let the eight cell masses `a, b, c, d, e, f, g, h` be
positive. If `G` and `E` are independent among the non-cases, `b h = d f`, then
`SOR = a g / (c e)`.

Source: VanderWeele et al. (2010), Appendix A, crediting Piegorsch et al. (1994). -/
theorem oddsRatioInteraction_eq_caseOnly {a b c d e f g h : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hf : 0 < f) (hg : 0 < g) (hh : 0 < h)
    (hind : b * h = d * f) :
    oddsRatioInteraction a b c d e f g h = caseOnlyOddsRatio a c e g := by
  unfold oddsRatioInteraction caseOnlyOddsRatio
  calc
    _ = a * g / (c * e) * (d * f / (b * h)) := by field_simp
    _ = _ := by rw [← hind, div_self (mul_ne_zero hb.ne' hh.ne'), mul_one]

/-- **Under dependence, the case-only odds ratio can differ from `1` without interaction.** There
are positive cell masses `a, b, c, d, e, f, g, h` with no multiplicative interaction on either
scale, `SRR = 1` and `SOR = 1`, whose case-only odds ratio `a g / (c e)` is not `1`; in such a law
`G` and `E` are dependent (VanderWeele et al. 2010). This is a counterexample: it exhibits one
such law, not a failure in every law where `G` and `E` are dependent.

Source: VanderWeele et al. (2010), on the sensitivity of the design to the independence
assumption; the example is derived. -/
theorem exists_caseOnly_ne_one :
    ∃ a b c d e f g h : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e ∧ 0 < f ∧ 0 < g ∧ 0 < h ∧
      riskRatioInteraction a b c d e f g h = 1 ∧ oddsRatioInteraction a b c d e f g h = 1 ∧
      caseOnlyOddsRatio a c e g ≠ 1 := by
  -- In each stratum the case and non-case masses are equal, so its risk is `1/2` and odds are `1`.
  refine ⟨1 / 6, 1 / 6, 1 / 12, 1 / 12, 1 / 12, 1 / 12, 1 / 6, 1 / 6, ?_⟩
  norm_num [riskRatioInteraction, oddsRatioInteraction, caseOnlyOddsRatio]

end WantedExt.Biology.StatisticalGenetics.CaseOnlyInteractionWanted

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The case-only design for gene–environment interaction

For a binary genotype `G`, a binary exposure `E` and a binary disease `D`, write the eight cell
masses of a finite joint law as `a, b` (cases, non-cases with `G = 0, E = 0`), `c, d`
(`G = 1, E = 0`), `e, f` (`G = 0, E = 1`) and `g, h` (`G = 1, E = 1`). The multiplicative
interaction on the risk-ratio scale is `SRR = RR_ge / (RR_g RR_e)` and on the odds-ratio scale
`SOR = OR_ge / (OR_g OR_e)`; the case-only odds ratio is `a g / (c e)`, computed from cases
alone.

If `G` and `E` are independent among the non-cases, `SOR = a g / (c e)` exactly (Piegorsch,
Weinberg and Taylor 1994). If `G` and `E` are independent in the population,
`SRR = a g / (c e)` exactly (Yang et al. 1999; Schmidt and Schaid 1999). With population
independence and a rare disease, `SOR` and `SRR` agree in the limit, so the case-only odds ratio
approximates both. Without independence the case-only odds ratio can differ from `1` when there
is no interaction on either scale.

Sources: W. W. Piegorsch, C. R. Weinberg and J. A. Taylor, "Non-hierarchical logistic models
and case-only designs for assessing susceptibility in population-based case-control studies",
Stat. Med. 13 (1994) 153–162; T. J. VanderWeele et al., "Case-only gene-environment
interaction studies: when does association imply mechanistic interaction?", Genet. Epidemiol.
34 (2010) 327–334, Table 1, Background and Appendix A.
-/
module

public import Batteries.Util.ProofWanted
public import Domains.Biology.StatisticalGenetics.AssociationTests.CaseOnlyInteraction
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.CaseOnlyInteractionWanted

open Filter Topology

/-- **Case-only odds ratio under non-case independence** (Piegorsch, Weinberg and Taylor 1994;
VanderWeele et al. 2010, Appendix A). Let the eight cell masses `a, b, c, d, e, f, g, h` be
positive. If `G` and `E` are independent among the non-cases, `b h = d f`, then
`SOR = a g / (c e)`.

Source: VanderWeele et al. (2010), Appendix A, crediting Piegorsch et al. (1994). -/
public theorem_wanted oddsRatioInteraction_eq_caseOnly {a b c d e f g h : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hf : 0 < f) (hg : 0 < g) (hh : 0 < h)
    (hind : b * h = d * f) :
    oddsRatioInteraction a b c d e f g h = caseOnlyOddsRatio a c e g

/-- **Case-only odds ratio under population independence** (VanderWeele et al. 2010,
Background). Let the eight cell masses `a, b, c, d, e, f, g, h` be positive. If `G` and `E` are
independent in the population, `(g + h)(a + b) = (c + d)(e + f)`, then `SRR = a g / (c e)`.

Source: VanderWeele et al. (2010), Background, crediting Yang et al. (1999) and Schmidt and
Schaid (1999). -/
public theorem_wanted riskRatioInteraction_eq_caseOnly {a b c d e f g h : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hf : 0 < f) (hg : 0 < g) (hh : 0 < h)
    (hind : (g + h) * (a + b) = (c + d) * (e + f)) :
    riskRatioInteraction a b c d e f g h = caseOnlyOddsRatio a c e g

/-- **Rare-disease limit** (VanderWeele et al. 2010). Let `G` and `E` be independent in the
population with `P(G = 1) = π_G ∈ (0, 1)` and `P(E = 1) = π_E ∈ (0, 1)`, and let the disease risk
in cell `(G, E) = (i, j)` be `ε ρ_{ij}` with `ρ_{00} = 1` and positive relative risks
`ρ_{10}, ρ_{01}, ρ_{11}`. Write the cell masses as risk times population frequency for cases and
`(1 - risk)` times frequency for non-cases. Then the odds-ratio interaction tends to
`ρ_{11} / (ρ_{10} ρ_{01})`, the risk-ratio interaction, as `ε → 0⁺`.

Source: VanderWeele et al. (2010), Background and Appendix A (the rare-disease approximation),
derived as a limit. -/
public theorem_wanted tendsto_oddsRatioInteraction_rare {πG πE ρ10 ρ01 ρ11 : ℝ}
    (hG0 : 0 < πG) (hG1 : πG < 1) (hE0 : 0 < πE) (hE1 : πE < 1) (h10 : 0 < ρ10) (h01 : 0 < ρ01)
    (h11 : 0 < ρ11) :
    Tendsto (fun ε : ℝ => oddsRatioInteraction
        (ε * ((1 - πG) * (1 - πE))) ((1 - ε) * ((1 - πG) * (1 - πE)))
        (ε * ρ10 * (πG * (1 - πE))) ((1 - ε * ρ10) * (πG * (1 - πE)))
        (ε * ρ01 * ((1 - πG) * πE)) ((1 - ε * ρ01) * ((1 - πG) * πE))
        (ε * ρ11 * (πG * πE)) ((1 - ε * ρ11) * (πG * πE)))
      (𝓝[>] 0) (𝓝 (ρ11 / (ρ10 * ρ01)))

end WantedExt.Biology.StatisticalGenetics.CaseOnlyInteractionWanted

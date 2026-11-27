# Fluctuation scaling exponent of semipushed waves

**Setting.** For a stochastic expansion front with carrying capacity $N$ governed by the reaction–diffusion model of the [classification of expansion waves by the velocity ratio](classification-of-expansion-waves-by-the-velocity-ratio.md), with demographic (number) fluctuations, let $\Lambda$ be the rate at which neutral genetic diversity (average heterozygosity $H$) at the front decays, $H(t) \propto e^{-\Lambda t}$, and let $D_f$ be the diffusion constant of the front position. Write $\Lambda \propto N^{\alpha_H}$ and $D_f \propto N^{\alpha_D}$ for large $N$.

**Result.** Both quantities scale with the same exponent, which depends only on $v/v_F$:

$$
\alpha_D = \alpha_H =
\begin{cases}
0, & v/v_F = 1,\\[1ex]
-\dfrac{2\sqrt{1 - v_F^2/v^2}}{1 - \sqrt{1 - v_F^2/v^2}}, & 1 < v/v_F < \tfrac{3}{2\sqrt2},\\[2ex]
-1, & v/v_F \ge \tfrac{3}{2\sqrt2}.
\end{cases}
$$

For pulled waves the power-law exponent is $0$ and the decay is logarithmic, $\Lambda \propto \ln^{-3} N$. Fully pushed waves follow central-limit scaling $N^{-1}$; in semipushed waves the exponent increases continuously from $-1$ to $0$ as $v/v_F$ decreases to $1$, so diversity loss and front wandering are much larger than in fully pushed waves even with an Allee effect.

## Depends on

- [Classification of expansion waves by the velocity ratio](classification-of-expansion-waves-by-the-velocity-ratio.md)

## Expansion

Perturbation theory expresses $\Lambda$ and $D_f$ as ratios of integrals of powers of the front profile, the numerators diverging at the leading edge in the semipushed regime. Cutting off the profile where the density falls to order one individual, at distance $\sim \ln N / k$, turns the divergence into the power law; the exponent is $(2v/D - 3k)/(\text{decay rate of the denominator})$ evaluated with $k$ from the edge equation. At $v/v_F = 3/(2\sqrt2)$ the formula equals $-1$, matching the fully pushed regime continuously.

## Sources

- G. Birzu, O. Hallatschek and K. S. Korolev, "Fluctuations uncover a distinct class of traveling waves", *Proceedings of the National Academy of Sciences USA* (2018), Eq. 8 and the surrounding text (front diffusion and rate of diversity loss). <https://doi.org/10.1073/pnas.1715737115> (PMC5910819)

# Selection index on breeding value and gametic variance for breeding top-ranking offspring

Consider an outbred population in which genomic estimated breeding values (GEBV) are scaled so that $\operatorname{Var}(\hat A) = 1$ in the unselected base population. For a selection candidate let $\hat A$ be its GEBV and $\sigma_{\hat g}$ the standard deviation of the GEBV of its gametes (its Mendelian sampling SD, which varies among individuals through heterozygosity and linkage phase). Mated to a random mate with GEBV $\hat A_{\mathrm{mate}}$ and expected gametic variance $1/4$, the candidate's offspring have GEBV with mean $\bar{\hat A}_{\mathrm{off}} = \tfrac12 \hat A + \tfrac12 \hat A_{\mathrm{mate}}$ and within-family SD

$$\sigma_{\widehat{MS}} = \sqrt{\sigma_{\hat g}^2 + 1/4}.$$

Let $p$ be the fraction of offspring defined as "top", $\tau_p$ the absolute truncation point in the offspring generation, $x_p$ the standard normal upper-tail truncation point ($1 - \Phi(x_p) = p$), $z_p = \varphi(x_p)$, and $i_p = z_p / p$ the selection intensity.

**Proposition (Bijma, Wientjes and Calus 2020, Appendix B).** Approximate the offspring GEBV of the candidate as normal, so the probability that one offspring ranks in the top $p$ is

$$P \approx \Phi\!\left( \frac{\bar{\hat A}_{\mathrm{off}} - \tau_p}{\sigma_{\widehat{MS}}} \right).$$

Linearizing $P$ in $(\hat A, \sigma_{\widehat{MS}})$ at population averages (where $P = p$ and the standardized truncation point equals $x_p$) gives partial derivatives $\partial P / \partial \hat A = z_p / (2\sigma)$ and $\partial P / \partial \sigma_{\widehat{MS}} = z_p\, x_p / \sigma$, so $P$ is, to first order, an increasing affine function of

$$I_7 = \hat A + 2 x_p\, \sigma_{\widehat{MS}}.$$

Further linearizing $\sigma_{\widehat{MS}}$ in $\sigma_{\hat g}$ around its mean $\sigma_{\hat g} \approx 1/2$, i.e. $\sigma_{\widehat{MS}} \approx \tfrac{1}{\sqrt 2} + \tfrac{1}{\sqrt 2}(\sigma_{\hat g} - \tfrac12)$, and dropping constants gives the index

$$I_5 = \hat A + \sqrt{2}\, x_p\, \sigma_{\hat g}.$$

The analogous index targeting the mean GEBV of selected offspring (response to recurrent selection), obtained from the predicted mean $\tfrac12(\hat A + \hat A_{\mathrm{mate}}) + i_p \sigma_{\widehat{MS}}$ of the selected offspring, is

$$I_8 = \hat A + 2 i_p\, \sigma_{\widehat{MS}}, \qquad I_6 = \hat A + \sqrt{2}\, i_p\, \sigma_{\hat g}.$$

Ranking candidates by $I_5$ instead of $\hat A$ therefore favours parents that produce more variable gametes, with a weight on $\sigma_{\hat g}$ that grows with the stringency $x_p$ of the "top" threshold.

## Depends on

- [Hazel's selection index](hazel-selection-index.md)
- [The Bulmer effect: selection reduces additive variance](../mendelian-segregation-and-the-infinitesimal-mode/bulmer-effect.md)

## Proof depends on

- [Standard normal CDF](../../../Probability/central-limit-theorems/berry-esseen-theorem/kolmogorov-distance/normal-cdf.md)
- [Standard Gaussian density function](../../../Probability/distributions/continuous/multivariate-normal-distribution/gaussian-density/std-gaussian-pdfreal.md)

## Expansion

Offspring GEBV equals the average of two parental gametic values, so the within-family variance is the sum of the two parents' gametic variances and the SD is $\sqrt{\sigma_{\hat g}^2 + \sigma_{\hat g,\mathrm{mate}}^2}$, not their sum. The chain rule gives $\partial P/\partial \hat A = \varphi(\cdot)\cdot \tfrac{1}{\sigma}\cdot\tfrac12$ and $\partial P / \partial \sigma = \varphi(\cdot)\,(\tau_p - \bar{\hat A}_{\mathrm{off}})/\sigma^2$; evaluated at population values and divided by $z_p/(2\sigma)$, this is $I_7$. The first-order Taylor expansion of $\sqrt{s^2 + 1/4}$ at $s = 1/2$ has slope $s/\sqrt{s^2 + 1/4} = 1/\sqrt 2$, which turns the weight $2x_p$ on $\sigma_{\widehat{MS}}$ into $\sqrt{2}\,x_p$ on $\sigma_{\hat g}$. In simulations based on dairy cattle parameters, $I_5$ was among the best of ten indices and raised the probability of breeding a top-0.1% genotype by about 36% in a population at Bulmer equilibrium.

## Sources

- P. Bijma, Y. C. J. Wientjes and M. P. L. Calus, "Breeding Top Genotypes and Accelerating Response to Recurrent Selection by Selecting Parents with Greater Gametic Variance", Genetics 214 (2020), 91–107, Methods (Indices 5–8) and Appendix B, <https://doi.org/10.1534/genetics.119.302643> (PMC6944402).

# Hazel's selection index: further results

Beyond the [selection index equations](hazel-selection-index.md), Hazel (1943, eq. (3)) gives the genetic gain from selection on the index $I$ as $\Delta\bar H = i\,R_{IH}\,\sigma_H$, where $H = \sum_ka_kG_k$ is the aggregate genotype, $i$ is the average superiority of the selected individuals' indexes over the whole group in standard-deviation units, $R_{IH}$ is the correlation between $I$ and $H$, and $\sigma_H$ the standard deviation of $H$. The formula holds exactly when $H$ has a linear regression on $I$, $E[H \mid I] = EH + \beta_{HI}(I - EI)$ with $\beta_{HI} = \mathrm{Cov}(H, I)/\sigma_I^2$ (for example under joint normality), and requires $\sigma_I > 0$ and $\sigma_H > 0$; the target is the formula with these hypotheses made explicit.

## Expansion

1. Selection on $I$ and the standardized selection differential $i = (E[I \mid \text{selected}] - EI)/\sigma_I$.
2. The gain $E[H \mid \text{selected}] - EH = \beta_{HI}(E[I \mid \text{selected}] - EI)$ under linear regression, hence $\Delta\bar H = i\sigma_H\mathrm{corr}(I, H)$.
3. The degenerate cases $\sigma_I = 0$ or $\sigma_H = 0$, and a non-linear regression where the formula fails.
4. Maximizing the gain for fixed $i$ by maximizing $\mathrm{corr}(I, H)$, which is the index of the candidate page.

## Sources

- L. N. Hazel, The genetic basis for constructing selection indexes, Genetics 28 (1943), 476–490. <https://doi.org/10.1093/genetics/28.6.476>

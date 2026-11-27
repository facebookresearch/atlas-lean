# Expected number of pre-existing multidrug-resistant cells

In the [multitype birth–death model of combination-therapy resistance](multitype-birth-death-model-of-combination-therapy-resistance.md) with two drugs, let $X$ be the number of type-$11$ cells (resistant to both drugs) when the lesion first reaches $M$ cells, and set

$$\mu = \frac{u \log(M s)}{s}, \qquad s = 1 - \frac{d}{b}.$$

In the regime of many cells and small mutation rate, to second order in $\mu$,

$$\mathbb{E}[X] \approx M\left[n_{12}\,\mu + \Bigl(n_1 n_2 + \frac{n_{12}}{2}\,(n_1 + n_2 - n_{12})\Bigr)\mu^2\right].$$

Consequently:

- if $n_{12} \ge 1$, then $\mathbb{E}[X] \approx M n_{12}\mu$, independent of $n_1, n_2$;
- if $n_{12} = 0$, then $\mathbb{E}[X] \approx M n_1 n_2 \mu^2$;
- for $k$ drugs without cross-resistance, $\mathbb{E}[X] \approx M n_1 n_2 \cdots n_k\, \mu^k$.

The probability that dual resistance is present at detection is $p_{\mathrm{res}} = 1 - p_1 p_2$, where $p_1$ (no resistance acquired in one mutational step) and $p_2$ (none acquired in two steps) are

$$p_1 = \exp\!\Bigl(\frac{M u\, n_{12} \log s}{1 - s}\Bigr), \qquad p_2 \approx \exp\!\Bigl[\frac{M u^2\,\bigl(2 n_1 n_2 + n_{12}(n_1 + n_2)\bigr) \log(s) \log(M s)}{s(1 - s)}\Bigr].$$

Since $\log s < 0$ and $Ms > 1$, both exponents are nonpositive; the one-step exponent vanishes when $n_{12} = 0$, and the two-step one when $2 n_1 n_2 + n_{12}(n_1 + n_2) = 0$. The factor $2 n_1 n_2 + n_{12}(n_1 + n_2)$ counts the two-step mutational paths to dual resistance.

## Depends on

- [Multitype birth–death model of resistance to combination therapy](multitype-birth-death-model-of-combination-therapy-resistance.md)

## Expansion

A resistant mutant arising when the total population is $x$ grows, conditioned on survival, roughly in proportion to $M/x$; summing over the births of the growing lesion produces the logarithmic factor $\log(Ms)/s$, which is why $\mu$ rather than $u$ is the effective per-cell rate. One-step resistance contributes linearly in $\mu$ and two-step resistance quadratically, so a single possible cross-resistance mutation dominates dual resistance whenever $n_{12} \ge 1$. With $u \approx 10^{-9}$ and $M$ of order $10^9$ to $10^{11}$ cells, $M n_{12}\mu$ is of order one or larger, while $M n_1 n_2 \mu^2$ can be far below one; this is the quantitative basis for requiring drugs with no shared resistance mutation. Proofs are in Supplementary file 1 of the source.

## Sources

- I. Bozic, J. G. Reiter, B. Allen, T. Antal, K. Chatterjee, P. Shah, et al., "Evolutionary dynamics of cancer in response to targeted combination therapy", *eLife* 2 (2013), e00747, Results (formula for $X$ and for $p_{\mathrm{res}} = 1 - p_1 p_2$), <https://doi.org/10.7554/eLife.00747> (PMC3691570).

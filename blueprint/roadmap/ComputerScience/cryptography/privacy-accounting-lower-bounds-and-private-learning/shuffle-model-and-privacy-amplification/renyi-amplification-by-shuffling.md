# Asymptotically optimal Rényi privacy amplification by shuffling

Let $R^{(1)}, \dots, R^{(n)}$ be local randomizers, where $R^{(i)}(z_{1:i-1}, \cdot)$ is $\varepsilon_0$-differentially private for all auxiliary inputs, and let $A_s$ apply them to the $n$ records in uniformly random order. There is an absolute constant $c$ such that for every order $1 < \alpha < n/(32\,\varepsilon_0 e^{\varepsilon_0})$ the shuffled output $A_s$ is $(\alpha, \alpha\rho)$-Rényi differentially private, that is, for all neighbouring datasets $X_0, X_1$,

$$
D_\alpha\big(A_s(X_0) \,\|\, A_s(X_1)\big) \le \alpha\rho, \qquad \rho \le c\,(1 - e^{-\varepsilon_0})^2\,\frac{e^{\varepsilon_0}}{n} = c\,\frac{(e^{\varepsilon_0} - 1)^2}{e^{\varepsilon_0}\, n},
$$

which is asymptotically optimal; for $\varepsilon_0 \ge 1$ this is $\rho \le c\,e^{\varepsilon_0}/n$. The same work also gave a sharper multinomial-based analysis of approximate-DP amplification with improved numerical bounds, but by the authors' erratum those improved general bounds, and their numerical comparisons, hold only for a restricted class of local randomizers admitting a suitable decomposition (including several important ones), not for all local randomizers.

## Proof sketch

By the clone reduction, it suffices to bound a divergence between two count distributions $(A + \Delta, C - A + 1 - \Delta)$ and $(A + 1 - \Delta, C - A + \Delta)$, where $C \sim \mathrm{Bin}(n-1, e^{-\varepsilon_0})$, $A \mid C \sim \mathrm{Bin}(C, 1/2)$ and $\Delta$ is an independent Bernoulli; any divergence satisfying the data-processing inequality, Rényi divergence included, is bounded this way. For $\varepsilon_0 \le 1$ the bound follows from earlier work. For $\varepsilon_0 \ge 1$, a tail bound on the privacy loss of this pair of count distributions, which is at most order $(1 - e^{-\varepsilon_0})\sqrt{e^{\varepsilon_0}\log(1/\delta)/n}$ except with probability $\delta$, is converted into a bound on Rényi divergences of orders up to order $n/(\varepsilon_0 e^{\varepsilon_0})$.

## Depends on

- [Zero-concentrated differential privacy](../zero-concentrated-differential-privacy/zero-concentrated-dp.md)
- [Local randomizers and the shuffle model](shuffle-model.md)

## Proof depends on

- [Shuffled local reports reduce to a binomial clone-counting problem](shuffle-clone-reduction.md)

## Sources

- V. Feldman, A. McMillan, K. Talwar, "Stronger Privacy Amplification by Shuffling for Renyi and Approximate Differential Privacy", SODA (2023), arXiv:2208.04591v2, Section 7 (Errata), Corollary 7.2 and Appendix B.

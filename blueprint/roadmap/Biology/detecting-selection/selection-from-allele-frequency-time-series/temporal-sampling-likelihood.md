# Forward recursion for allele-frequency time series with absorbing transitions

Consider the hidden Markov likelihood of Bollback, York and Nielsen (2008) for samples of $y_k$ derived alleles out of $n_k$ genes taken at times $t_1 < \dots < t_K$, with the population frequency evolving by a Wright–Fisher diffusion with selection and binomial emissions $P(y \mid x) = \binom{n}{y}x^y(1 - x)^{n - y}$. They compute the likelihood by a recursion over sampling times that is the forward algorithm with the sum over states replaced by an integral (Methods). Because the frequency can be absorbed between samples, the transition law $K_\Delta(x, \cdot)$ over a time $\Delta$ is a measure with an interior density and atoms at $0$ and $1$ (Zhao, Lascoux, Overall and Waxman 2013, Appendix A). The recursion is therefore an integral against this measure: with $\alpha_1(dx) = \pi_0(dx)P(y_1 \mid x)$ for the law $\pi_0$ of the frequency at $t_1$,

$$\alpha_{k+1}(dx') = P(y_{k+1} \mid x')\int\alpha_k(dx)\,K_{t_{k+1} - t_k}(x, dx'),$$

and the likelihood of the data is $\alpha_K([0, 1])$. On the atoms the emissions are $P(y \mid 0) = \mathbf 1\{y = 0\}$ and $P(y \mid 1) = \mathbf 1\{y = n\}$, so a sample with $0 < y < n$ assigns zero weight to an absorbed path. The recursion is correct because the frequency process is Markov and the samples are conditionally independent given the frequencies at the sampling times: $\alpha_k(B)$ is the joint probability of $y_1, \dots, y_k$ and of $X_{t_k} \in B$, by induction on $k$. A recursion that uses only the interior transition density omits the atoms and undercounts the probability of samples fixed for one allele.

## Depends on

- [Hidden Markov likelihood for allele-frequency time series](../../../Biology/detecting-selection/selection-from-allele-frequency-time-series/hmm-likelihood-for-allele-frequency-time-series.md)

## Expansion

1. The transition laws of the diffusion with selection as measures with interior densities and atoms at $0$ and $1$.
2. The forward recursion over these measures, and its proof by induction from the Markov property and conditional independence.
3. The contribution of the atoms through the emissions at $0$ and $1$.
4. Numerical transition laws (discretized diffusion equations, spectral expansions) as approximations of $K_\Delta$, and the resulting error in the likelihood.

## Sources

- J. P. Bollback, T. L. York and R. Nielsen, Estimation of 2Nes from temporal allele frequency data, Genetics 179 (2008), 497–502, Methods. <https://doi.org/10.1534/genetics.107.085019>
- S. Zhao, M. Lascoux, A. D. J. Overall and D. Waxman, The characteristic trajectory of a fixing allele: a consequence of fictitious selection that arises from conditioning, Genetics 195 (2013), 993–1006, Appendix A. <https://doi.org/10.1534/genetics.113.156059>

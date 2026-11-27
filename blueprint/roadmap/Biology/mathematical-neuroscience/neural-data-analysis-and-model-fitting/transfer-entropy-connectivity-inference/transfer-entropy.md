# Transfer entropy

Let $(I_n)$ and $(J_n)$ be jointly stationary processes with values in finite sets, and for a Markov order $k \ge 1$ write $i^{(k)}_n = (i_n, i_{n-1}, \dots, i_{n-k+1})$ for the vector of the last $k$ values of $I$ up to time $n$, and similarly $j^{(k)}_n$. The **transfer entropy** from $J$ to $I$ is

$$\mathrm{TE}_{J \to I} = \sum_{i_{n+1},\, i^{(k)}_n,\, j^{(k)}_n} P\big(i_{n+1}, i^{(k)}_n, j^{(k)}_n\big) \log \frac{P\big(i_{n+1} \mid i^{(k)}_n, j^{(k)}_n\big)}{P\big(i_{n+1} \mid i^{(k)}_n\big)} .$$

The sum runs over the finitely many values with $P\big(i_{n+1}, i^{(k)}_n, j^{(k)}_n\big) > 0$, so every term is finite.

Properties:

- $\mathrm{TE}_{J \to I}$ is the expected Kullback–Leibler divergence between the "two-node" transition law $P(i_{n+1} \mid i^{(k)}_n, j^{(k)}_n)$ and the "single-node" law $P(i_{n+1} \mid i^{(k)}_n)$, equivalently the conditional mutual information $I(I_{n+1}; J^{(k)}_n \mid I^{(k)}_n)$;
- $\mathrm{TE}_{J \to I} \ge 0$, with equality if and only if $I_{n+1}$ is conditionally independent of $J^{(k)}_n$ given $I^{(k)}_n$, i.e. the transitions of $I$ do not depend statistically on the past of $J$;
- it is asymmetric in general, so it measures directed influence, and it detects non-linear dependence that linear measures such as cross-correlation or linear Granger causality can miss.

## Expansion

Because the alphabets are finite, all entropies below are finite, and writing the logarithm of the ratio as a difference of conditional entropies gives $\mathrm{TE}_{J \to I} = H(I_{n+1} \mid I^{(k)}_n) - H(I_{n+1} \mid I^{(k)}_n, J^{(k)}_n)$, which is non-negative because conditioning cannot increase entropy; Gibbs' inequality applied for each value of the conditioning variables gives the equality case. For countably infinite alphabets this difference can be $\infty - \infty$ (a target process of infinite entropy, independent of the source, has transfer entropy $0$), which is why the definition is the log-ratio sum and the alphabets are finite. In practice the probabilities are estimated by histograms after quantizing continuous signals into a small number of levels, and all directed pairs of nodes are scored and ranked.

## Sources

- O. Stetter, D. Battaglia, J. Soriano and T. Geisel, "Model-free reconstruction of excitatory neuronal connectivity from calcium imaging signals", PLoS Computational Biology 8 (2012), e1002653, Methods ("Generalized Transfer Entropy"), Eq. (9), <https://doi.org/10.1371/journal.pcbi.1002653> (PMC3426566).
- T. Schreiber, "Measuring information transfer", Physical Review Letters 85 (2000), 461–464, <https://doi.org/10.1103/PhysRevLett.85.461>.

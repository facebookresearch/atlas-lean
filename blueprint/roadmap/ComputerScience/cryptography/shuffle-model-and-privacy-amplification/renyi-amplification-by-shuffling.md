# Asymptotically optimal Rényi privacy amplification by shuffling

For shuffled outputs of $\varepsilon_0$-differentially private local randomizers applied to $n$ records, the Rényi differential privacy parameter of order $\alpha$ is bounded by

$$
D_\alpha\big(A_s(X_0) \,\|\, A_s(X_1)\big) \le O\!\left(\frac{\alpha\,(e^{\varepsilon_0} - 1)^2}{e^{\varepsilon_0}\, n}\right)
$$

for $\alpha$ in a range growing with $n e^{-\varepsilon_0}$, which is asymptotically optimal, together with an improved approximate-DP analysis of shuffling that yields tighter numerical bounds than the clone analysis in all parameter regimes.

## Proof sketch

By the clone reduction, it suffices to bound the Rényi divergence between two binomial-type count distributions differing by one shifted Bernoulli. Expanding the $\alpha$-th moment of their likelihood ratio, which is a polynomial in the shift probability, and using binomial moment bounds conditioned on the number of clones gives a divergence of order $\alpha$ times the squared bias divided by the number of clones, which is about $n e^{-\varepsilon_0}$.

## Depends on

- [Shuffled local reports reduce to a binomial clone-counting problem](shuffle-clone-reduction.md)
- [Zero-concentrated differential privacy](../zero-concentrated-differential-privacy/zero-concentrated-dp.md)

## Proof depends on

- [Shuffled local reports reduce to a binomial clone-counting problem](shuffle-clone-reduction.md)
- [Zero-concentrated differential privacy](../zero-concentrated-differential-privacy/zero-concentrated-dp.md)

## Sources

- V. Feldman, A. McMillan, K. Talwar, "Stronger Privacy Amplification by Shuffling for Renyi and Approximate Differential Privacy", SODA (2023), arXiv:2208.04591.

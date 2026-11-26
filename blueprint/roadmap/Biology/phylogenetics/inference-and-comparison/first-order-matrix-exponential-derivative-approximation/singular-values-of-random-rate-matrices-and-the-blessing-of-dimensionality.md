# Singular values of random rate matrices and the blessing of dimensionality

Let $F_X$ be a sub-exponential distribution of a nonnegative random variable with mean $\mu > 0$ and variance $\sigma^2 > 0$. Consider random rate matrices $Q = Q(d) \in \mathbb{R}^{d\times d}$ with nonnegative off-diagonal entries and rows summing to zero, where either the off-diagonal entries are i.i.d. draws from $F_X$ and $-q_{ii} = \sum_{j \ne i} q_{ij}$, or $Q$ is symmetric with its above-diagonal entries i.i.d. from $F_X$. Order the singular values as $\sigma_1(Q) \le \dots \le \sigma_d(Q)$. Then, almost surely,

$$\mu + O_{a.s.}\!\left(\sqrt{\frac{\log d}{d}}\right) \le \frac{\sigma_2(Q)}{d} \le \frac{\sigma_d(Q)}{d} \le \mu + O_{a.s.}\!\left(\sqrt{\frac{\log d}{d}}\right).$$

In the symmetric case $\sigma_j(Q) = |\lambda_{d-j+1}(Q)|$, so all nonzero eigenvalues have modulus of order $\mu d$. Feeding this into the dimension-dependent bound for the first-order derivative approximation gives: for such symmetric random rate matrices and every direction $J$, the error of

$$\hat\nabla_J e^{tQ} := t e^{tQ}J - t(I - Q^+Q)JQQ^+$$

relative to $\nabla_J e^{tQ}$ is bounded in operator norm by a term decaying like $e^{-t\mu_1 d}$ plus $\frac{2}{\mu_1 d}\|J\|_{op}$, so the corrected first-order approximation improves as the number of states $d$ grows.

## Depends on

- [Affine-corrected error bound for the first-order matrix exponential derivative](affine-corrected-error-bound-for-the-first-order-matrix-exponential-derivative.md)

## Expansion

A random rate matrix is a centred random matrix plus a large deterministic part: the diagonal entries are sums of $d-1$ i.i.d. terms and concentrate at $-(d-1)\mu$, while the off-diagonal fluctuations have spectral norm of smaller order. Concentration for sub-exponential sums controls both pieces uniformly, placing all singular values except the trivial one at $\mu d(1 + O(\sqrt{\log d/d}))$. The spectral gap therefore grows linearly in $d$, which is exactly the quantity that controls the exponential decay and the $1/d$ remainder in the error bound. The correction term reuses the spectral decomposition already needed for $e^{tQ}$, so it adds little cost.

## Sources

- G. Didier, N. E. Glatt-Holtz, A. J. Holbrook, A. F. Magee and M. A. Suchard, "On the surprising effectiveness of a simple matrix exponential derivative approximation, with application to global SARS-CoV-2", *Proceedings of the National Academy of Sciences* 121 (2024), e2318989121, Definition 1, Theorem 3, Eq. (45), Corollary 1, and Remark 5, Eq. (46). <https://doi.org/10.1073/pnas.2318989121> (PMC10801879)

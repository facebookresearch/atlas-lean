# Low-degree threshold of the spiked Wigner model

Let $\mathbb{Q}_n$ be the law of a symmetric Gaussian Wigner matrix $W$ (independent $\mathcal{N}(0,1/n)$ off-diagonal entries) and $\mathbb{P}_n$ the law of $Y = \frac{\lambda}{n}xx^\top + W$ with $x$ having i.i.d. Rademacher entries (more generally, i.i.d. entries from a fixed subgaussian prior with unit variance). If $\lambda < 1$ is fixed, then $\|L_n^{\le D}\| = O(1)$ for every $D = o(n)$, while for $\lambda > 1$ strong detection is achieved in polynomial time by the largest eigenvalue (which separates from the bulk edge $2$), and $\|L_n^{\le D}\| \to \infty$ for $D \ge C\log n$. For sparse priors (sparse PCA), the low-degree analysis predicts the conjectured computational thresholds strictly above the information-theoretic ones.

## Proof sketch

By the additive Gaussian lemma (after rescaling), $\|L_n^{\le D}\|^2 = \sum_{d \le D}\frac{1}{d!}\big(\frac{\lambda^2}{2n}\big)^d\mathbb{E}[\langle x, x'\rangle^{2d}]$, and $\langle x, x'\rangle/\sqrt{n}$ is a normalized Rademacher sum with subgaussian moments, so for $d \ll n$ the $d$-th term is close to $\lambda^{2d}\mathbb{E}[g^{2d}]/(2^d d!) = \lambda^{2d}\binom{2d}{d}4^{-d}$ with $g$ standard Gaussian, and $\sum_d \lambda^{2d}\binom{2d}{d}4^{-d} = (1-\lambda^2)^{-1/2} < \infty$ for $\lambda < 1$. For $\lambda > 1$, the BBP transition places the top eigenvalue at $\lambda + 1/\lambda > 2$.

## Depends on

- [Low-degree advantage of the additive Gaussian model](additive-gaussian-low-degree-advantage.md)

## Proof depends on

- [Low-degree advantage of the additive Gaussian model](additive-gaussian-low-degree-advantage.md)

## Sources

- D. Kunisky, A. S. Wein, A. S. Bandeira, "Notes on Computational Hardness of Hypothesis Testing: Predictions Using the Low-Degree Likelihood Ratio", Mathematical Analysis, its Applications and Computation, Springer (2022), arXiv:1907.11636.
- S. B. Hopkins, "Statistical Inference and the Sum of Squares Method", PhD thesis, Cornell University (2018).

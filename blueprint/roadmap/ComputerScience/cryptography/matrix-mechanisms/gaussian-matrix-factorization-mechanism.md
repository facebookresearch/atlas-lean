# Gaussian matrix-factorization mechanism

Let $n, k, d \ge 1$. Let $A \in \mathbb{R}^{n \times n}$ be a query matrix with a factorization $A = BC$, where $B \in \mathbb{R}^{n \times k}$ and $C \in \mathbb{R}^{k \times n}$. Let $\gamma = \max_i \|C_{:,i}\|_2$ be the largest Euclidean norm of a column of $C$. Fix $\zeta \ge 0$, and call data matrices $G, H \in \mathbb{R}^{n \times d}$ neighbouring when they differ in a single row and the Euclidean norm of the difference of that row is at most $\zeta$.

Let $0 < \varepsilon < 1$, $0 < \delta < 1$ and $c > 0$ with $c^2 > 2\ln(1.25/\delta)$, and let $\sigma > 0$ with $\sigma \ge c\gamma\zeta/\varepsilon$. Let $Z \in \mathbb{R}^{k \times d}$ have independent $\mathcal{N}(0, \sigma^2)$ entries. Then the mechanism $G \mapsto B(CG + Z)$, which estimates $AG$, is $(\varepsilon, \delta)$-differentially private for this neighbouring relation, with the data matrix fixed in advance (non-adaptive).

The prefix-sum workload, the lower-triangular all-ones matrix $S$, is the case used for private continual release of cumulative sums. Binary-tree mechanisms give particular factorizations of $S$ when $n$ is a power of two; other lengths can be zero-padded to such a horizon.

## Proof sketch

Flattening $k \times d$ matrices to vectors in $\mathbb{R}^{kd}$ turns the Frobenius norm into the Euclidean norm. By the sensitivity bound, the query $G \mapsto CG$ has Euclidean sensitivity at most $\gamma\zeta$. Hence $CG + Z$ is the Gaussian mechanism for that query, which is $(\varepsilon, \delta)$-differentially private under the stated calibration. The map $Y \mapsto BY$ is linear, hence measurable, and post-processing preserves differential privacy.

## Depends on

- [Differential privacy](../differential-privacy/differentially-private.md)

## Proof depends on

- [Sensitivity of a matrix factorization](matrix-factorization-sensitivity.md)
- [The Gaussian mechanism](../differential-privacy/gaussian-mechanism-differentially-privat.md)
- [Post-processing by a measurable map](../differential-privacy/map.md)

## Sources

- S. Denisov, H. B. McMahan, K. Rush, A. Smith and A. Thakurta, "Improved Differential Privacy for SGD via Optimal Private Linear Operators on Adaptive Streams", NeurIPS 2022, arXiv:2202.08312v3, Section 1, equation (1) (the factorization mechanism $B(CG + Z)$ and the prefix-sum matrix $S$), Appendix C (rectangular binary-tree factorizations), and Theorem 3.1 (the source states its own Gaussian variance, $\gamma^2\zeta^2(2\log(1/\delta) + \varepsilon)/\varepsilon^2$, adapted from Li et al.; this page uses the calibration below instead).
- C. Li, G. Miklau, M. Hay, A. McGregor and V. Rastogi, "The matrix mechanism: optimizing linear counting queries under differential privacy", The VLDB Journal 24 (2015) 757–781.
- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, Theorem A.1 (the Gaussian calibration used above).

# Gaussian matrix-factorization mechanism

Let $n, d \ge 1$, let $A \in \mathbb{R}^{n \times n}$ be a query matrix of full rank $n$ with a fixed factorization $A = BC$, where $B, C \in \mathbb{R}^{n \times n}$, and let $\gamma = \max_{1 \le i \le n} \|C_{:,i}\|_2$ be the largest Euclidean norm of a column of $C$. Fix $\zeta \ge 0$. Data matrices are matrices $G \in \mathbb{R}^{n \times d}$ each of whose rows has Euclidean norm at most $\zeta$; two of them are *neighbouring* when they differ in a single row and the Euclidean norm of the difference of that row is at most $\zeta$.

Let $\varepsilon > 0$ and $0 < \delta < 1$, and put

$$
\sigma^2 \;=\; \frac{\gamma^2\zeta^2\,\bigl(2\ln(1/\delta) + \varepsilon\bigr)}{\varepsilon^2}.
$$

Since $A = BC$ has full rank, $C$ is invertible, so $\gamma > 0$ and $\sigma^2 = 0$ exactly when $\zeta = 0$. If $\zeta > 0$, let $Z \in \mathbb{R}^{n \times d}$ have independent normal entries with mean $0$ and variance $\sigma^2$; if $\zeta = 0$, let $Z = 0$.

Then the algorithm that, given a data matrix $G$ fixed in advance (not chosen adaptively), outputs $B(CG + Z)$ as an estimate of $AG$ is $(\varepsilon, \delta)$-differentially private for this neighbouring relation.

The factors are square and $A$ has full rank, as the source assumes throughout. Singular query matrices, factorizations with a rectangular encoder $C \in \mathbb{R}^{k \times n}$, such as the binary-tree factorizations of the prefix-sum matrix, adaptively chosen rows, and other Gaussian calibrations are not covered by this statement.

## Proof sketch

By the sensitivity bound, $\|CG - CH\|_F \le \gamma\zeta$ for neighbouring $G, H$. If $\zeta = 0$, neighbouring data matrices are equal and the claim is immediate. Flattening $n \times d$ matrices to vectors in $\mathbb{R}^{nd}$ turns the Frobenius norm into the Euclidean norm, so for $\zeta > 0$, $CG + Z$ is the Gaussian mechanism for a query of Euclidean sensitivity at most $\gamma\zeta$ with the variance above. The map $Y \mapsto BY$ is linear, hence measurable, and post-processing preserves differential privacy.

## Depends on

- [Differential privacy](../differential-privacy/differentially-private.md)

## Proof depends on

- [Sensitivity of a matrix factorization](matrix-factorization-sensitivity.md)
- [Post-processing by a measurable map](../differential-privacy/map.md)

## Expansion

This page becomes ready once:

- The Gaussian mechanism at this calibration: for a query with Euclidean sensitivity at most $\Delta > 0$, adding independent normal noise of variance $\Delta^2(2\ln(1/\delta) + \varepsilon)/\varepsilon^2$ to each coordinate is $(\varepsilon, \delta)$-differentially private for every $\varepsilon > 0$ and $0 < \delta < 1$ (proof prerequisite; not yet stated). The existing [Gaussian mechanism](../differential-privacy/gaussian-mechanism-differentially-privat.md) page assumes $\varepsilon < 1$ and $\sigma \ge c\Delta/\varepsilon$ with $c^2 > 2\ln(1.25/\delta)$, which does not cover this variance for all such $\varepsilon$.

## Sources

- S. Denisov, H. B. McMahan, K. Rush, A. Smith and A. Thakurta, "Improved Differential Privacy for SGD via Optimal Private Linear Operators on Adaptive Streams", NeurIPS 2022, arXiv:2202.08312v3: Section 1 (the query matrix $A$ is assumed to be full rank throughout the work), Definition 3.1 (neighbouring data matrices, assumed for the rest of the paper) and Theorem 3.1 (fixed square factorization, fixed data matrix with rows of Euclidean norm at most $\zeta$, the variance above; the source writes $\log$ for the natural logarithm and states the theorem as adapted from Li et al.).

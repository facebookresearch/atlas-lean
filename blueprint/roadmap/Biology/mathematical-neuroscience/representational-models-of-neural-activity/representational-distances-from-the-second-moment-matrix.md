# Representational distances from the second-moment matrix

With $U \in \mathbb{R}^{K \times P}$ the condition-by-channel activity patterns and $G = U U^{\mathsf T}/P$ their second-moment matrix, the squared Euclidean distance between the patterns of conditions $i$ and $k$, normalized by the number of channels, is

$$d_{i,k} = \frac{(u_{i,\cdot} - u_{k,\cdot})(u_{i,\cdot} - u_{k,\cdot})^{\mathsf T}}{P} = G_{i,i} - 2G_{i,k} + G_{k,k}. \tag{19}$$

1. With a contrast matrix $C$ whose rows have a $1$ and a $-1$ for each pair of conditions, the vector of all pairwise distances is $d = \operatorname{diag}(C G C^{\mathsf T})$ (Eq. 21); the cosine distance $1 - G_{k,i}/\sqrt{G_{i,i}G_{k,k}}$ is also a function of $G$ (Eq. 20).
2. Let $D$ be the $K \times K$ matrix of the $d_{i,k}$ and $H = I_K - \mathbf{1}\mathbf{1}^{\mathsf T}/K$ the centring matrix. If the patterns are centred ($\mathbf{1}^{\mathsf T} U = 0$, equivalently every row and column of $G$ sums to zero), then

$$G = -\tfrac{1}{2} H D H. \tag{22}$$

Without centring, $D$ determines $G$ only up to the distances of the patterns to the baseline.
3. **Cross-validated estimate.** Let $\hat u^{(m)}_{i,\cdot} = u_{i,\cdot} + \varepsilon^{(m)}_{i,\cdot}$ be (prewhitened) pattern estimates from $M \ge 2$ independent partitions, with noise independent across partitions and of mean zero, and let $\hat u^{(\sim m)}$ be the average over the partitions other than $m$. The crossnobis estimator

$$\hat d_{i,k} = \frac{1}{M}\sum_{m=1}^{M} \frac{(\hat u^{(m)}_{i,\cdot} - \hat u^{(m)}_{k,\cdot})(\hat u^{(\sim m)}_{i,\cdot} - \hat u^{(\sim m)}_{k,\cdot})^{\mathsf T}}{P} \tag{23}$$

is unbiased for $d_{i,k}$ (computed from the prewhitened true patterns), whereas the non-cross-validated squared distance of noisy estimates is biased upward by the noise variance.

## Depends on

- [Second-moment matrix and linear decodability](second-moment-matrix-and-linear-decodability.md)

## Expansion

Expanding the squared norm in (19) gives the identity with $G$. Writing $g = \operatorname{diag}(G)$, (19) reads $D = g\mathbf{1}^{\mathsf T} + \mathbf{1} g^{\mathsf T} - 2G$; since $H\mathbf{1} = 0$, $HDH = -2HGH$, and $HGH = G$ for centred patterns. For (23), the two factors involve noise from disjoint partitions, so the expectation of each product is $(u_i - u_k)(u_i - u_k)^{\mathsf T}$: all cross terms have zero mean. Multivariate noise normalization (prewhitening by the estimated noise covariance) turns Euclidean into Mahalanobis distances. The crossnobis estimates are approximately multivariate normal with a covariance that depends on $G$, which gives a likelihood for representational similarity analysis (Eqs. 26–30).

## Sources

- J. Diedrichsen, N. Kriegeskorte, "Representational models: a common framework for understanding encoding, pattern-component, and representational-similarity analysis", PLoS Computational Biology 13(4) (2017) e1005508, Eqs. (1), (19)–(23), (26)–(30), <https://doi.org/10.1371/journal.pcbi.1005508> (PMC5421820).

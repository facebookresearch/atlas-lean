# Rademacher complexity of VC classes without a logarithmic factor

There is an absolute constant $c_0$ with the following property. Let $C$ be a class of functions $X \to \{0,1\}$ all of whose finite shattered sets have at most $d \ge 1$ points, and $\sigma(C)$ its $\pm 1$-valued sign class. For every $m > 0$ and every sample of $m$ points, the empirical Rademacher complexity satisfies

$$
\hat{R}_S(\sigma(C)) \le c_0\sqrt{\frac{d}{m}}.
$$

If $X$ is a measurable space, $C$ consists of measurable functions (with the usual measurability of the suprema involved) and $X_1, \ldots, X_m$ are independent with law $\mu$, then $\mathbb{E}\sup_{c \in C}\big|\frac1m\sum_{i} c(X_i) - \mathbb{E}_\mu c\big| \le c_0\sqrt{d/m}$, and the same bound holds for the Rademacher complexity of $\sigma(C)$ under $\mu$. Consequently, for every distribution $D$ on $X \times \{0,1\}$, with probability at least $1 - \delta$ an empirical risk minimizer $A$ for $C$ satisfies $\mathrm{err}_D(A(S)) \le \mathrm{err}_D(c) + c_0\sqrt{d/m} + \sqrt{2\ln(2/\delta)/m}$ for every $c \in C$: an excess error $O(\sqrt{(d + \ln(1/\delta))/m})$.

## Proof sketch

Conditionally on the sample, the Rademacher process $Z_c = m^{-1/2}\sum_i \varepsilon_i\, c(X_i)$ has sub-gaussian increments in the empirical $L^2$ distance, so Dudley's inequality bounds $\mathbb{E}_\varepsilon \sup_c Z_c$ by an absolute constant times $\int_0^1 \sqrt{\ln N(C, L^2(\mu_m), \varepsilon)}\,d\varepsilon$, and the VC covering bound $\ln N(C, L^2(\mu_m), \varepsilon) \lesssim d\ln(2/\varepsilon)$ makes the integral at most an absolute constant times $\sqrt d$. Passing from $C$ to $\sigma(C) = \{2c - 1\}$ doubles the complexity, symmetrization gives the empirical-process form, and the ERM bound follows as for the logarithmic VC rate.

Explicit constant: on a sample, sign patterns of two labelings at Hamming distance $t$ are at Euclidean distance $2\sqrt{t}$. A maximal separated set of labelings at Hamming scale $m/4^{n+1}$ is a Euclidean net at scale $\sqrt{m}/2^n$ with at most $2^{2d(2n+5)}$ points by Dudley's packing bound. Dyadic chaining with these nets and the trivial net $\{0\}$ at the top sums to $32\sqrt{d/m}$, so $c_0 = 32$ works in the first display.

## Depends on

- [Empirical Rademacher complexity](../rademacher-complexity/rademacher-complexity.md)
- [Rademacher complexity of a VC class, explicit rate](../rademacher-complexity/rademacher-complexity-sign-patterns-le-v.md)
- [Dudley's entropy bound](../../../../Probability/high-dimensional-probability/generic-chaining-and-gaussian-processes/integral-i-sup-le-dudley.md)

## Proof depends on

- [Dudley's packing bound for classes of bounded VC dimension](../../pac-learning/sample-complexity-and-combinatorial-dimensions/packing-and-one-inclusion-graphs/dudley-packing-bound-for-vc-classes.md)
- [Rademacher and VC bounds for binary classification](rademacher-bounds-for-binary-classification.md)

## Sources

- S. Shalev-Shwartz and S. Ben-David, "Understanding Machine Learning: From Theory to Algorithms", Cambridge University Press, 2014.
- R. Vershynin, "High-Dimensional Probability: An Introduction with Applications in Data Science", Cambridge University Press, 2018, Theorem 8.3.23 and its proof.

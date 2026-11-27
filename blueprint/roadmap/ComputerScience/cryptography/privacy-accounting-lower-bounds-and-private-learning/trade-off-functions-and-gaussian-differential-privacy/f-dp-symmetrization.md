# Symmetrization of f-differential privacy guarantees

If a mechanism is $f$-DP, then it is also $f^{-1}$-DP, where $f^{-1}(\alpha) = \inf\{t \in [0,1] : f(t) \le \alpha\}$, and hence it is $\mathrm{Symm}(f)$-DP for the symmetric trade-off function

$$
\mathrm{Symm}(f) = \max\{f, f^{-1}\},
$$

which is already convex as a maximum of two convex functions, and satisfies $\mathrm{Symm}(f)^{-1} = \mathrm{Symm}(f)$; here $f^{-1}$ is again a trade-off function, being the trade-off function of the pair with the hypotheses exchanged. In particular every privacy guarantee can be taken symmetric without loss, and for the Gaussian and $(\varepsilon,\delta)$ families $G_\mu^{-1} = G_\mu$ and $f_{\varepsilon,\delta}^{-1} = f_{\varepsilon,\delta}$.

## Proof sketch

The neighbouring relation is symmetric, so $T(M(S'), M(S)) \ge f$ also holds; for any pair, $T(Q, P) = T(P, Q)^{-1}$ because exchanging the hypotheses exchanges type I and type II errors, which reflects the error region across the diagonal. Hence $T(M(S), M(S')) \ge f^{-1}$, and the maximum of two lower bounds is a lower bound; it is a trade-off function by the characterization, being convex, continuous, nonincreasing and at most $1 - \alpha$.

## Depends on

- [f-differential privacy](f-differential-privacy.md)
- [Gaussian differential privacy](gaussian-differential-privacy.md)

## Proof depends on

- [Characterization of trade-off functions](trade-off-function-characterization.md)

## Sources

- J. Dong, A. Roth, W. J. Su, "Gaussian Differential Privacy", Journal of the Royal Statistical Society Series B 84 (2022), arXiv:1905.02383v3, Proposition 2.4.

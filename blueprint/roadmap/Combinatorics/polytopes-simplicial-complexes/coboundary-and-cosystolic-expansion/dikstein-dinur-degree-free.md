# Dikstein–Dinur: cosystolic expansion without dependence on dimension or degree

Let $\beta, \lambda > 0$ and $k \ge 1$, let $X$ be a $d$-dimensional $\lambda$-one-sided local spectral expander with $d \ge k + 2$, and let $\Gamma$ be a group (abelian if $k > 1$). If for every non-empty face $r$ of $X$ the link $X_r$ satisfies $h^{k+1-|r|}(X_r, \Gamma) \ge \beta$, then the cosystolic expansion constant of $X$ in dimension $k$ satisfies

$$
h^k(X, \Gamma) \ge \frac{\beta^{k+1}}{4\,(k+2)!} - e\lambda,
$$

a bound that depends on neither $d$ nor the degree of $X$.

## Proof sketch

Instead of iterating correction steps through all dimensions, one uses a single color-restriction argument: restrict the cochain to a random partite sub-complex of constant dimension and apply the local hypothesis through a carefully chosen chain of link averages. Local spectral expansion controls the error of each averaging step uniformly, which removes the exponential dependence on $d$ present in earlier local-to-global proofs.

## Depends on

- [Coboundary expansion of a simplicial complex](coboundary-expansion.md)
- [Cosystolic expansion and cosystolic distance](cosystolic-expansion.md)
- [Non-abelian 1-cochains and unique-games coboundary expansion](nonabelian-cochain.md)

## Proof depends on

- [Evra–Kaufman: bounded-degree cosystolic expanders of every dimension](evra-kaufman-every-dimension.md)

## Sources

- Y. Dikstein, I. Dinur, "Coboundary and cosystolic expansion without dependence on dimension or degree", APPROX-RANDOM (2023), ECCC TR23-043.

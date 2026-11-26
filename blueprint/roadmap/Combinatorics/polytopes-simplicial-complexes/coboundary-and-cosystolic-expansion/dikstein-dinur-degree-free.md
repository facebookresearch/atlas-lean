# Dikstein–Dinur: cosystolic expansion without dependence on dimension or degree

There are absolute constants $c, \lambda_0 > 0$ such that the following holds for every $d \ge 3$, every $1 \le i \le d-2$ and every coefficient group (abelian or not, for $i = 1$). If $X$ is a $d$-dimensional $\lambda$-local spectral expander with $\lambda \le \lambda_0$ and all links of $(i-1)$-faces are $\beta$-coboundary expanders in dimension $i$, then $X$ is an $(\varepsilon, \mu)$-cosystolic expander in dimension $i$ with

$$
\varepsilon \ge c \cdot \beta, \qquad \mu \ge c \cdot \beta,
$$

independently of $d$ and of the maximal vertex degree.

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

# Statistically indistinguishable ensembles are computationally indistinguishable

Let $X$ and $Y$ be distribution ensembles on bit strings that are statistically indistinguishable, with negligible distance bound $\varepsilon(n)$. Then $X \approx_c Y$: for every distinguisher $D$ (efficient or not) and every $n$, the distinguishing advantage of $D$ at parameter $n$ is at most $\varepsilon(n)$. In particular the conclusion holds for all probabilistic polynomial-time distinguishers, and the ensembles need not be efficiently samplable.

## Proof sketch

For a fixed $n$ and fixed coins of $D$, the event that $D$ outputs $1$ is an event $E$ on samples, so its probabilities under $X_n$ and $Y_n$ differ by at most $\varepsilon(n)$. Averaging over the coins of $D$ preserves the bound.

## Depends on

- [Statistical indistinguishability of distribution ensembles](statistical-indistinguishability-of-ensembles.md)
- [Computational indistinguishability of distribution ensembles](computational-indistinguishability-of-ensembles.md)

## Proof depends on

- [Statistical distance bounds advantage](../games-and-advantages/advantage-map-le-dist.md)

## Sources

- O. Goldreich, "Foundations of Cryptography, Volume 1: Basic Tools", Cambridge University Press, 2001, Section 3.2.2.

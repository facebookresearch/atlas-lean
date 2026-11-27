# Averaging bound for games with a common first stage

Let $\mu$ be a distribution on a set $S$ and, for each $s \in S$, let $G_0(s)$ and $G_1(s)$ be Boolean experiments. Let $G_b$ denote the experiment that samples $s \leftarrow \mu$ and runs $G_b(s)$. Then

$$\bigl|\Pr[G_0 = 1] - \Pr[G_1 = 1]\bigr| \le \mathbb{E}_{s \leftarrow \mu}\bigl[\,|\Pr[G_0(s)=1] - \Pr[G_1(s)=1]|\,\bigr].$$

If the first stages also differ, with laws $\mu_0, \mu_1$, then the advantage is at most $\Delta(\mu_0, \mu_1)$ plus the above expectation taken under $\mu_1$.

## Proof sketch

Write both success probabilities as integrals over the first stage and apply the triangle inequality inside the integral; the second claim inserts the hybrid that runs $G_0$'s second stage on $\mu_1$ and bounds its distance to the first by the statistical distance of the first stages.

## Depends on

- [Distinguishing advantage](../games-and-advantages/advantage.md)
- [Total variation distance between finite measures](../../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Proof depends on

- [Triangle inequality](../games-and-advantages/advantage-triangle.md)
- [Statistical distance bounds advantage](../games-and-advantages/advantage-map-le-dist.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- V. Shoup, "Sequences of Games: A Tool for Taming Complexity in Security Proofs", IACR Cryptology ePrint Archive, Report 2004/332, 2004.

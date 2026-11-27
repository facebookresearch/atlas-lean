# Lumping property of f-divergences

For $f$ convex on $[0,\infty)$, $P \ge 0$, $Q > 0$ and any map $g : \alpha \to \beta$ between finite
alphabets,

$$D_f(P^g \| Q^g) \le D_f(P \| Q),$$

where $P^g, Q^g$ are the [lumpings](lumping-of-a-distribution.md) along $g$. Merging letters cannot
increase an f-divergence: this is data processing for deterministic maps. Proof: apply the
[generalised log-sum inequality](generalised-log-sum-inequality.md) on each fibre of $g$.
Compared with the source, $Q$ is assumed strictly positive and $f$ finite at $0$.

## Sources

- I. Csiszár and P. C. Shields, *Information Theory and Statistics: A Tutorial*, Foundations and Trends in Communications and Information Theory 1(4) (2004), 417–528, Lemma 4.1 (lumping property).

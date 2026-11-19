# One Edmonds–Karp step does not shorten distances from the source (Proposition 3 (1))

Let $f'$ be the result of one step of the [Edmonds–Karp algorithm](edmonds-karp.md) from a flow $f$: augmentation by the bottleneck along the shortest residual path from $s$ to $t$ returned by breadth-first search, or $f' = f$ when $t$ is unreachable. Then every walk of length $\ell$ from $s$ to a vertex $u$ in the residual graph of $f'$ can be replaced by a walk of length at most $\ell$ from $s$ to $u$ in the residual graph of $f$: $\delta^k(s, u) \le \delta^{k+1}(s, u)$ in Edmonds and Karp's notation, including the case $\delta^{k+1}(s, u) = \infty$.

## Informally uses

- [New residual arcs reverse the augmenting path (Edmonds–Karp, Proposition 2)](residual-graph-edge-augment.md): the hypothesis of the abstract statement.
- [Distances from the source do not decrease (abstract form of Edmonds–Karp, Proposition 3 (1))](relates-within-steps-source-of-shortest.md): the combinatorial core.
- [Soundness of the shortest-path search](shortest-path-sound.md): the path used by the step is a shortest residual path.

## Sources

- J. Edmonds and R. M. Karp, "Theoretical improvements in algorithmic efficiency for network flow problems", *Journal of the ACM* 19(2) (1972), 248–264, §1.2 (Propositions 2 and 3, Lemmas 1 and 2, Theorem 1).

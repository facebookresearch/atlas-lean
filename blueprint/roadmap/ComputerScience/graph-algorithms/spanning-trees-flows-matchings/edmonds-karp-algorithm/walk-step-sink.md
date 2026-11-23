# One Edmonds–Karp step does not shorten distances to the sink (Proposition 3 (2))

For one step of the [Edmonds–Karp algorithm](edmonds-karp.md) from $f$ to $f'$, every walk of length $\ell$ from a vertex $u$ to $t$ in the residual graph of $f'$ can be replaced by a walk of length at most $\ell$ from $u$ to $t$ in the residual graph of $f$: $\delta^k(u, t) \le \delta^{k+1}(u, t)$.

## Informally uses

- [New residual arcs reverse the augmenting path (Edmonds–Karp, Proposition 2)](residual-graph-edge-augment.md): the hypothesis of the abstract statement.
- [Distances to the sink do not decrease (abstract form of Edmonds–Karp, Proposition 3 (2))](relates-within-steps-sink-of-shortest.md): the combinatorial core.
- [Soundness of the shortest-path search](shortest-path-sound.md): the path used by the step is a shortest residual path.

## Sources

- J. Edmonds and R. M. Karp, "Theoretical improvements in algorithmic efficiency for network flow problems", *Journal of the ACM* 19(2) (1972), 248–264, §1.2 (Propositions 2 and 3, Lemmas 1 and 2, Theorem 1).

# Scott's graph theorem, part (ii)

Every set $u \subseteq \mathbb{N}$ is contained in the graph of the function it determines: $u \subseteq \operatorname{graph}(x \mapsto \operatorname{app}(u, x))$ (D. Scott, *Data types as lattices*, SIAM J. Comput. 5(3) (1976), 522–587, Theorem 1.2 (ii)). Scott's proof takes, for $\langle n, m\rangle \in u$, the finite set $e_n$ itself as the witness.

Equality holds exactly when $u$ is upward closed in its first coordinate (Theorem 1.2 (iii)).

## Background

- [Scott's graph theorem, part (i)](app-graph.md): the other half of the retraction.
- [Scott's graph theorem, part (iii)](graph-app-eq-iff.md): when the inclusion is an equality.
- [The graph model is not extensional](exists-graph-app-ne.md): the inclusion can be strict.

## Sources

- D. Scott, *Data types as lattices*, SIAM Journal on Computing 5(3) (1976), 522–587, doi:10.1137/0205037.

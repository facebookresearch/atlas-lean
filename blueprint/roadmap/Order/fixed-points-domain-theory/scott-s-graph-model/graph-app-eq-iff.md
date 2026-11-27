# Scott's graph theorem, part (iii)

A set $u \subseteq \mathbb{N}$ is the graph of the function it determines, $\operatorname{graph}(\operatorname{app}(u, \cdot)) = u$, exactly when $u$ is upward closed in the first coordinate: $\langle k, m\rangle \in u$ and $e_k \subseteq e_n$ imply $\langle n, m\rangle \in u$ (D. Scott, *Data types as lattices*, SIAM J. Comput. 5(3) (1976), 522–587, Theorem 1.2 (iii)). Scott notes that this condition is equivalent to $u = \lambda x.\, u(x)$, so the sets satisfying it are exactly the graphs (Appendix A, remarks after the proof of Theorem 2.2).

## Background

- [Scott's graph theorem, part (ii)](subset-graph-app.md): the inclusion that always holds.
- [The graph model is not extensional](exists-graph-app-ne.md): a set for which the condition fails.

## Sources

- D. Scott, *Data types as lattices*, SIAM Journal on Computing 5(3) (1976), 522–587, doi:10.1137/0205037.

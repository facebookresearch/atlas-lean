# Meta-operation tree and probe attribution

Fix fanouts $\lambda_1, \lambda_2, \dots \ge 2$ and block sizes $m_0 = 1$, $m_\ell = m_{\ell-1} \lambda_\ell$. Over the $N$ meta-operations of a run of a cell-probe scheme on a hard dictionary distribution, each meta-operation is a level-0 node, and each level-$\ell$ node is the parent of a group of $\lambda_\ell$ consecutive level-$(\ell-1)$ nodes, so that it represents an interval of $m_\ell$ consecutive meta-operations (assuming $m_\ell$ divides $N$ below the top level); a single root at the top level $h$ represents all $N$ meta-operations. For a node $u$:

- if a cell is probed during meta-operations $t_1 < t_2$ and during no meta-operation strictly between them, the probe at $t_2$ is *assigned* to the lowest common ancestor of $t_1$ and $t_2$, and $\mathrm{cost}_u$ is the number of probes assigned to $u$;
- $\mathrm{probe}_u$ is the number of probes made while processing the meta-operations of the interval of $u$.

Every probe is assigned to at most one node, so the total probe count of the run is at least $\sum_u \mathrm{cost}_u$; for each fixed level $\ell$, the sum of $\mathrm{probe}_u$ over the level-$\ell$ nodes equals the total probe count of the meta-operations.

## Depends on

- [Deterministic dynamic cell-probe scheme](../cell-probe-complexity/deterministic-cell-probe-scheme.md)
- [Hard operation distributions for dynamic dictionaries](hard-operation-distributions.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Tight Cell-Probe Lower Bounds for Dynamic Succinct Dictionaries", Proceedings of the 64th IEEE Symposium on Foundations of Computer Science (FOCS), pp. 1842-1862, 2023; arXiv:2306.02253.
- M. Patrascu and E. D. Demaine, "Logarithmic Lower Bounds in the Cell-Probe Model", SIAM Journal on Computing 35(4), pp. 932-963, 2006.

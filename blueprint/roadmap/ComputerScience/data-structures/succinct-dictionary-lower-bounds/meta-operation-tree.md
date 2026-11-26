# Meta-operation tree and probe attribution

Fix even fanouts $\lambda_1, \lambda_2, \dots \ge 2$ and set block sizes $m_0 = 1$, $m_{\ell+1} = m_\ell \lambda_{\ell+1}$. At level $\ell$ the time line of $N$ meta-operations is cut into $\lfloor N / m_\ell \rfloor$ consecutive blocks of $m_\ell$ meta-operations (nodes); the children of a level-$(\ell+1)$ node are its $\lambda_{\ell+1}$ level-$\ell$ blocks. A cell probe made during meta-operation $t$ to a cell last written during meta-operation $t' < t$ is *attributed* to the lowest common ancestor of $t'$ and $t$; a probe to a cell never written before is attributed to no node. Every probe is attributed to at most one node, so the total probe count of the run is at least the sum, over all nodes, of the probes attributed to them.

## Depends on

- [Deterministic dynamic cell-probe scheme](../cell-probe-complexity/deterministic-cell-probe-scheme.md)
- [Hard operation distributions for dynamic dictionaries](hard-operation-distributions.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Tight Cell-Probe Lower Bounds for Dynamic Succinct Dictionaries", Proceedings of the 64th IEEE Symposium on Foundations of Computer Science (FOCS), 2023; arXiv:2306.02253.
- M. Patrascu and E. D. Demaine, "Logarithmic Lower Bounds in the Cell-Probe Model", SIAM Journal on Computing 35(4), 2006.

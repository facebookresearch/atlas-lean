# Aggregating level bounds over the meta-operation tree

Let a meta-operation tree for the hard distribution have levels $1, \dots, H$, and suppose that for each level $\ell$ the expected number of probes attributed to its nodes is at least $\beta_\ell$. Then the expected total number of probes is at least $\sum_{\ell=1}^H \beta_\ell$. For the iterated-logarithm schedule with fanouts chosen so that $\log_2 \lambda_\ell \ge \gamma^{-1} c_R \log^{(k)} n$, there are at least $k - O(1)$ levels whose blocks are at most $n/2$, and for the geometric schedule with constant fanout there are at least $\log_2(n / \max(R, 1)) - O(1)$ such levels.

## Proof sketch

Attributions to distinct nodes are disjoint, so the attributed probes over all levels sum to at most the total. The level counts follow from the explicit fanout schedules: iterating the exponential $k$ times from the leaves reaches block size about $n$, and doubling from block size $R$ reaches $n/2$ after $\log_2(n/R)$ steps.

## Depends on

- [Meta-operation tree and probe attribution](meta-operation-tree.md)
- [Iterated logarithm and log-star](../hashing/succinct-dictionaries-and-hash-families/dictionary-specifications/iterated-logarithm.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Tight Cell-Probe Lower Bounds for Dynamic Succinct Dictionaries", Proceedings of the 64th IEEE Symposium on Foundations of Computer Science (FOCS), 2023; arXiv:2306.02253.

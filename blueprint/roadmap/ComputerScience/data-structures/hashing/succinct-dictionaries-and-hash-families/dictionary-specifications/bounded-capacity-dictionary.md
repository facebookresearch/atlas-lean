# Bounded-capacity dictionary specification

Let $U, V, n_{\max}$ be natural numbers. The *bounded-capacity dictionary* over keys $[U] = \{0, \dots, U-1\}$ with values below $V$ has states $s : [U] \to \{\bot\} \cup \mathbb{N}$ (with $\mathrm{dom}(s) = \{u : s(u) \ne \bot\}$), initial state $s \equiv \bot$, and operations $\mathrm{query}(u)$, returning $s(u)$, and $\mathrm{insert}(u, v)$, setting $s(u) := v$. An insertion is admissible iff $v < V$ and either $|\mathrm{dom}(s)| < n_{\max}$ or $u \in \mathrm{dom}(s)$ (in-place overwrite). The *dynamic dictionary* additionally has $\mathrm{delete}(u)$, setting $s(u) := \bot$ (a no-op when $u$ is absent). This is the dictionary problem of Li, Liang, Yu and Zhou (a set of at most $n_{\max}$ keys of $[U]$ with values in $[V]$, under insertions, deletions and queries).

## Depends on

- [State-transition specification of a data structure](../../../data-structure-interfaces-and-refinement/state-transition-specification.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009, Chapter 11.
- T. Li, J. Liang, H. Yu and R. Zhou, "Tight Cell-Probe Lower Bounds for Dynamic Succinct Dictionaries", Proceedings of the 64th IEEE Symposium on Foundations of Computer Science (FOCS), pp. 1842-1862, 2023; arXiv:2306.02253.

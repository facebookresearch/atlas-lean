# Theta equals the independence number on perfect graphs

If the finite graph $G$ is [perfect](../../graph-coloring/part-01/perfect-graphs/is-perfect.md), then $\vartheta(G) = \alpha(G)$. By Lovász's perfect graph theorem the complement $\bar G$ is perfect, so applied to the whole vertex set $\chi(\bar G) = \omega(\bar G) = \alpha(G)$, and the [sandwich theorem](sandwich.md) $\alpha(G) \le \vartheta(G) \le \chi(\bar G)$ collapses. Together with the polynomial-time computability of $\vartheta$, this is how Grötschel, Lovász and Schrijver compute $\alpha$, $\omega$ and $\chi$ of perfect graphs in polynomial time.

## Sources

- D. E. Knuth, *The Sandwich Theorem*, Electron. J. Combin. 1 (1994), #A1, arXiv:math/9312214v1, eq. (4.9) and §31.
- A. Schrijver, *A Course in Combinatorial Optimization* (CWI lecture notes), Corollary 7.7a (Lovász's perfect graph theorem).

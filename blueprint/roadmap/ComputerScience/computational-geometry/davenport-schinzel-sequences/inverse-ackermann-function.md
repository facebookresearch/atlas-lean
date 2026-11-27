# Inverse Ackermann function

Define functions $\alpha_k : \mathbb{N} \to \mathbb{N}$ by $\alpha_1(n) = \lceil n/2 \rceil$ and, for $k \ge 2$,

$$\alpha_k(n) = \begin{cases} 0 & \text{if } n \le 1, \\ 1 + \alpha_k(\alpha_{k-1}(n)) & \text{otherwise,} \end{cases}$$

so that $\alpha_k(n)$ counts how often $\alpha_{k-1}$ must be applied to $n$ to reach a value at most $1$; for example $\alpha_2(n) = \lceil \log_2 n \rceil$ and $\alpha_3(n) = \log^* n$. The *inverse Ackermann function* is $\alpha(n) = \min\{k \ge 1 : \alpha_k(n) \le 3\}$. For each fixed $k$, $\alpha_k(n) = o(\alpha_{k-1}(n))$ and $\alpha(n) = o(\alpha_k(n))$.
## Related topics

- [Inverse Ackermann function of Tarjan and van Leeuwen](../../data-structures/disjoint-sets-and-dynamic-trees/disjoint-set-data-structure/inverse-ackermann-tv-l.md): a two-argument form used for disjoint sets, different from this one.
- [Inverse Ackermann function](../../../Geometry/discrete-geometry/part-01/continuous-tur-n-numbers-of-planar-patterns/inverse-ackermann.md): a differently defined function.

## Sources

- *Computational Geometry*, lecture notes, ETH Zürich, autumn 2013, Chapter 12 (Davenport–Schinzel sequences), <https://ti.inf.ethz.ch/ew/courses/CG13/lecture/Chapter%2012.pdf>: the paragraph before Section 12.1 defining $\alpha_1, \alpha_2, \dots$ and $\alpha(n) = \min\{k \mid \alpha_k(n) \le 3\}$

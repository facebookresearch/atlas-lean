# Approximating the diameter with a well-separated pair decomposition

Let $P$ be a set of $n \ge 2$ points in $\mathbb{R}^d$, for fixed $d$, and let $0 < \varepsilon \le 1$. Take an $s$-WSPD of $P$ of size $O(s^d n)$, as given by the existence theorem, with $s = 4/\varepsilon$, choose a representative point in each set of each pair, and return the pair of representatives at largest distance. Its distance $D'$ satisfies $\operatorname{diam}(P)/(1 + \varepsilon) \le D' \le \operatorname{diam}(P)$, and the computation takes $O(n \log n + n/\varepsilon^d)$ time.

## Depends on

- [Well-separated pair decomposition](well-separated-pair-decomposition.md)

## Proof depends on

- [Existence of linear-size well-separated pair decompositions](existence-of-linear-size-well-separated-pair-decompositions.md)
- [Distances within a well-separated pair](distances-within-a-well-separated-pair.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 17, "Approximating the Diameter": $s = 4/\varepsilon$, the bound $\|x - y\| \le (1 + \varepsilon)\|p_u - p_v\|$ and the $O(n \log n + n/\varepsilon^d)$ running time

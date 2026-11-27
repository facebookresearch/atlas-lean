# Partial concept classes and their VC and Littlestone dimensions

A **partial concept** on a domain $X$ is a function $h : X \to \{0,1,\star\}$, where $h(x) = \star$ means that $h$ is undefined at $x$; its support is $\mathrm{supp}(h) = h^{-1}(\{0,1\})$. A **partial concept class** is a set $H \subseteq \{0,1,\star\}^X$. A finite labelled sample $((x_1,y_1), \dots, (x_n,y_n))$ with $y_i \in \{0,1\}$ is **realizable** by $H$ if some $h \in H$ has $h(x_i) = y_i$ for all $i$ (in particular all $x_i$ lie in its support), and a distribution $P$ on $X \times \{0,1\}$ is realizable if, for every $n$, an i.i.d. sample of size $n$ from $P$ is realizable with probability one. A set $\{x_1, \dots, x_d\}$ is **shattered** if every $y \in \{0,1\}^d$ is realized, and $\mathrm{VC}(H)$ is the largest size of a shattered set; Littlestone trees and $\mathrm{LD}(H)$ are defined as for total classes, using realizability of the branches. Total classes are the special case in which no concept takes the value $\star$.

## Depends on

- [The Littlestone dimension is the optimal mistake bound](../../../../online-learning-and-boosting/the-littlestone-dimension-is-the-optimal-mistake-bound.md)

## Sources

- N. Alon, S. Hanneke, R. Holzman, S. Moran, "A Theory of PAC Learnability of Partial Concept Classes", FOCS (2021), arXiv:2107.08444, Section 2.1, Definition 2 and Appendix C (Definitions 26 and 27).

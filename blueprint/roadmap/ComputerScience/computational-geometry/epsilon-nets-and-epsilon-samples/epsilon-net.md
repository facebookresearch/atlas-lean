# ε-net and ε-sample of a range space

A *range space* is a pair $(X, R)$ of a set $X$ and a family $R$ of subsets of $X$ (*ranges*). For $Y \subseteq X$ let $R|_Y = \{r \cap Y : r \in R\}$; $Y$ is *shattered* if $R|_Y$ contains every subset of $Y$, and the *VC dimension* of $(X, R)$ is the largest size of a shattered subset of $X$ ($\infty$ if there are arbitrarily large ones). For a finite nonempty $x \subseteq X$ and $r \in R$, the *measure* of $r$ is $m(r) = |r \cap x| / |x|$.

For $0 \le \varepsilon \le 1$, a subset $N \subseteq x$ (possibly a multiset) is an *$\varepsilon$-net* for $x$ if every range $r \in R$ with $m(r) \ge \varepsilon$ contains a point of $N$. A nonempty subset $C \subseteq x$ (possibly a multiset) is an *$\varepsilon$-sample* for $x$ if $|m(r) - |C \cap r| / |C|| \le \varepsilon$ for every range $r \in R$, counting $C \cap r$ with multiplicity.

## Sources

- S. Har-Peled, *Geometric Approximation Algorithms*, revised online chapter "On complexity, sampling, ε-nets and ε-samples" (Chapter 7), <https://sarielhp.org/book/chapters/vc_dim.pdf>: Definitions 7.1.1, 7.1.2 and 7.1.4 (range spaces, measure, shattering and VC dimension), Definition 7.3.1 (ε-sample) and Definition 7.3.3 (ε-net)
- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 36, "Range Spaces" and the definition of VC-dimension

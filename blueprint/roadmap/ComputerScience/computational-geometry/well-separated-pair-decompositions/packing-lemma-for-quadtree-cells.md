# Packing lemma for quadtree cells

Let $b$ be a ball of radius $r$ in $\mathbb{R}^d$ and let $X$ be a collection of pairwise interior-disjoint cells of a quadtree on $[0,1]^d$ (cubes $\prod_{i=1}^d [k_i 2^{-j}, (k_i + 1) 2^{-j}]$ with integers $j \ge 0$ and $0 \le k_i < 2^j$), each of side length at least $x$, that all meet $b$. Then

$$|X| \le \Big(1 + \Big\lceil \frac{2r}{x} \Big\rceil\Big)^d = O\Big(\max\Big(2, \frac{r}{x}\Big)^d\Big).$$

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 16, the Packing Lemma and its proof by counting grid cubes of side $x$ meeting a cube of side $2r$

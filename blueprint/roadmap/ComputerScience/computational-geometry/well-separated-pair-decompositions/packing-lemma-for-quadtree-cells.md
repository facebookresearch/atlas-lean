# Packing lemma for quadtree cells

Let $d \ge 1$ be fixed, let $b$ be a ball of radius $r > 0$ in $\mathbb{R}^d$, let $x > 0$, and let $X$ be a collection of pairwise interior-disjoint cells of a quadtree on $[0,1]^d$ (cubes $\prod_{i=1}^d [k_i 2^{-j}, (k_i + 1) 2^{-j}]$ with integers $j \ge 0$ and $0 \le k_i < 2^j$), each of side length at least $x$, that all overlap $b$, that is, meet its interior. Then

$$|X| \le \Big(1 + \Big\lceil \frac{2r}{x} \Big\rceil\Big)^d = O\Big(\max\Big(2, \frac{r}{x}\Big)^d\Big).$$

Each cell is a union of grid cubes of side $x_0$, the least power of $2$ that is at least $x$, one of which meets the interior of $b$; along each axis an open interval of length $2r$ meets at most $\lceil 2r/x_0 \rceil + 1$ grid intervals of length $x_0$.

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 16, the Packing Lemma and its proof by counting grid cubes of side $x$ meeting a cube of side $2r$

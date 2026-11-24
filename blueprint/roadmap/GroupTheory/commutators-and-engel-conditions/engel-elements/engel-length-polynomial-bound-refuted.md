# Engel lengths of products admit no polynomial bound (Kourovka 11.88)

There is a group $G$
such that for every polynomial $\varphi(x, y)$ in two variables with natural-number coefficients
there are $u, v \in G$ such that $u$, $v$ and $uv$ are Engel elements and
$l(uv) > \varphi(l(u), l(v))$. Here $g \in G$ is an Engel element if there is a $k \ge 1$ with
$[h, g; k] = 1$ for all $h \in G$, and its Engel length $l(g)$ is the least such $k$, where
$[h, g; 0] = h$, $[h, g; i + 1] = [[h, g; i], g]$ and $[x, y] = x^{-1} y^{-1} x y$.

For a prime $p$, Dolbak builds finite $p$-groups $G_n$ (wreath products of a cyclic group of
order $p$ by groups $K_n$) with elements $c_n$ and $c_n^{-1} b_0$ of Engel length at most
$(n + 1)p - n + 1$ whose product $b_0$ has Engel length at least $p^n$. He takes the direct
product of the $G_n$ in the restricted sense (the direct sum, whose elements have finite support).
It is a single Engel group: an element of finite support has Engel length at most the largest
Engel length of its coordinates, and each $G_n$ is a finite $p$-group, hence nilpotent. (The
unrestricted product is not Engel: the element with $b_0$ in every coordinate has unbounded Engel
length.) Let $u_n$ and $v_n$ be $c_n$ and $c_n^{-1} b_0$ in coordinate $n$ and $1$ elsewhere: they
are Engel elements of length at most $(n + 1)p - n + 1$, and $u_n v_n$ has length at least $p^n$,
which exceeds every polynomial in the lengths of the factors (Theorem 1: there are Engel groups in
which the Engel length of a product of two elements is bounded by no polynomial in the Engel
lengths of the factors). The refutation of this statement uses only that $u_n$, $v_n$ and
$u_n v_n$ are Engel elements of one group. The Kourovka Archive answers 11.88 "No, it does not".

## Sources

- E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.88 (V. A. Roman'kov); resolution: L. V. Dolbak, The Engel length of the product of Engel elements, Siberian Math. J. 47, no. 1 (2006), 55-57, Theorem 1 and its proof; Kourovka Archive, Problem 11.88: "No, it does not", https://doi.org/10.1007/s11202-006-0006-9.

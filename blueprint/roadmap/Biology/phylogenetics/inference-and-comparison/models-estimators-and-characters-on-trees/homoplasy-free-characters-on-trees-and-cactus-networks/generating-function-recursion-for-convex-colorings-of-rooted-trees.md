# Generating-function recursion for convex colorings of rooted trees

**Setting.** Convex colorings and their minimal extensions are as in the companion article; $\mathcal T$ is an arbitrary rooted phylogenetic tree (internal vertices may have any out-degree $d\ge 2$) and $\mathcal T_v$ is the subtree rooted at $v$. A coloring of $\mathcal T_v$ is *semiminimal* if it is induced on $\mathcal T_v$ by a minimal coloring of a larger tree containing $\mathcal T_v$ as a pendant subtree. For each vertex $v$ and $k\ge 1$ let $f_k(v)$ be the number of minimal $k$-colorings of $\mathcal T_v$ in which at least two children of $v$ share a color (then $v$ has that color), $g_k(v)$ the number of semiminimal $k$-colorings in which $v$ shares its color with exactly one child, and $h_k(v)$ the number of minimal $k$-colorings in which $v$ is uncolored. Put $F_v(x)=\sum_k f_k(v)x^k$, $G_v(x)=\sum_k g_k(v)x^k$, $H_v(x)=\sum_k h_k(v)x^k$.

**Theorem.** For a leaf $v$, $F_v=x$ and $G_v=H_v=0$. If $v$ has children $u_1,\dots,u_d$, then

$$ H_v(x)=\prod_{i=1}^d \bigl(F_{u_i}(x)+H_{u_i}(x)\bigr), \qquad G_v(x)=H_v(x)\sum_{i=1}^d \frac{F_{u_i}(x)+G_{u_i}(x)}{F_{u_i}(x)+H_{u_i}(x)} , $$

$$ F_v(x)=x\prod_{i=1}^d \Bigl(F_{u_i}(x)+H_{u_i}(x)+\frac{F_{u_i}(x)+G_{u_i}(x)}{x}\Bigr)-x\,H_v(x)-G_v(x) . $$

The number of convex $k$-colorings of the leaves of $\mathcal T$ is $f_k(r)+h_k(r)$ for the root $r$, so the total $p(\mathcal T)$ is $F_r(1)+H_r(1)$.

## Depends on

- [Number of convex colorings of a rooted binary tree](number-of-convex-colorings-of-a-rooted-binary-tree.md)

## Expansion

At an uncolored $v$ the children's subtrees are colored independently by minimal colorings ($F+H$ each). If $v$ is colored, the set $I$ of children sharing its color contributes semiminimal colorings of type $F+G$ divided by $x$ (the shared color is counted once), the others minimal colorings; expanding the product over all subsets and removing $|I|=0$ (the term $xH_v$) and $|I|=1$ (the term $G_v$) gives $F_v$. The recursion is computed bottom-up in polynomial time. The paper extends it to *cactus networks* (rooted networks whose underlying undirected graph is a cactus, so each edge lies on at most one cycle, generalizing galled trees) by an inclusion–exclusion over the two branches between a source and its sink.

## Sources

- N. Alexeev and M. A. Alekseyev, *Combinatorial scoring of phylogenetic networks*, arXiv:1602.02841 (2016). <https://doi.org/10.48550/arXiv.1602.02841> Lemma 1 and Theorem 2 (Section 2.1); Theorem 3 (Section 2.2) for the cactus-network extension. Published version: Lecture Notes in Computer Science 9797 (2016), 560-572, <https://doi.org/10.1007/978-3-319-42634-1_45>.

# Stable sets have total cost at most one

Let $a$ be an orthogonal labeling of $G$, let $c$ be any vector and let $S$ be a stable set of $G$ (no two of its vertices are adjacent). Then

$$
\sum_{v \in S} \mathrm{cost}_c(a_v) \le 1 .
$$

The nonzero vectors $a_v/\lVert a_v\rVert$, $v \in S$, are orthonormal because $S$ is stable, so Bessel's inequality gives $\sum_{v \in S} \langle a_v/\lVert a_v\rVert, c\rangle^2 \le \lVert c\rVert^2$; dividing by $\lVert c\rVert^2$ is the claim. Vertices with $a_v = 0$ have cost $0$, and every cost is $0$ when $c = 0$. Knuth proves the same inequality by completing the orthonormal vectors to an orthogonal matrix.

## Sources

- D. E. Knuth, *The Sandwich Theorem*, Electron. J. Combin. 1 (1994), #A1, arXiv:math/9312214v1, Lemma 1, eq. (1.1).

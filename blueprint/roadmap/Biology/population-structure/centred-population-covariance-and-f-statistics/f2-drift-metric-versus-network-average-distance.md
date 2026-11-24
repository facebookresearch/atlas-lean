# f2, independent-lineage distance and average network distance differ on admixture graphs

In a [drift model](../patterson-s-f-statistics/drift-model.md) on an admixture graph with lineage weights $w(X, e) \in [0, 1]$ and drift lengths $\ell_e \ge 0$, [f2 is](../patterson-s-f-statistics/f2-freq.md) $f_2(X, Y) = \sum_e (w(X, e) - w(Y, e))^2 \ell_e$. If
instead the lineages of $X$ and $Y$ are traced independently, with $w(X, e)$ the probability that the lineage of $X$ uses $e$, the expected length of edges used by exactly one
of them is

$$\sum_e \bigl(w(X, e) + w(Y, e) - 2w(X, e)w(Y, e)\bigr) \ell_e = f_2(X, Y) + h(X) + h(Y), \qquad h(X) = \sum_e w(X, e)\bigl(1 - w(X, e)\bigr) \ell_e ,$$

since $w_X + w_Y - 2w_Xw_Y - (w_X - w_Y)^2 = w_X(1 - w_X) + w_Y(1 - w_Y)$. The two agree on trees, where every weight is $0$ or $1$ and both equal the path length between $X$ and $Y$. Xu and Ané's average distance $\bar d(X, Y)$ is a third
quantity: the expected path length between $X$ and $Y$ in a random displayed tree, obtained by keeping one parent edge at each admixture node with its
inheritance probability. On a tree there is one displayed tree, so $\bar d$ is the path length as well and all three coincide. In the graph with root $R$, edges $R \to P$ of length $p$ and $R \to Q$ of length $q$, leaves $A$ below $P$ (length $a$) and $B$ below $Q$, and an
admixed leaf $C$ that takes proportion $\gamma$ from $P$ and $1 - \gamma$ from $Q$ through hybrid edges of length $0$ and then has a pendant edge of length $c$,

$$f_2(A, C) = a + c + (1 - \gamma)^2 (p + q), \qquad \bar d(A, C) = a + c + (1 - \gamma)(p + q) ,$$

which differ by $\gamma(1 - \gamma)(p + q) > 0$ whenever $0 < \gamma < 1$ and $p + q > 0$; here $h(A) = 0$ and $h(C) = \gamma(1 - \gamma)(p + q) > 0$, and $\bar d(A, C)$ happens to equal the independent-lineage distance $f_2(A, C) + h(A) + h(C)$.

## Depends on

- [Admixture-graph drift model](../patterson-s-f-statistics/drift-model.md)

## Proof depends on

- [f2 in the drift model](../patterson-s-f-statistics/f2-freq.md)

## Sources

- J. Xu and C. Ané, "Identifiability of local and global features of phylogenetic networks from average distances", arXiv:2110.11814, Definition 7.

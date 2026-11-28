# Support set of a two-colored best match graph

**Setting.** A leaf-colored rooted tree $(T,\sigma)$ with leaf set $L$ and coloring $\sigma:L\to\{r,s\}$ explains the *best match graph* (BMG) $\mathcal{G}(T,\sigma)$: there is an arc $x\to y$ for $\sigma(x)\ne\sigma(y)$ whenever $\operatorname{lca}_T(x,y)\preceq_T\operatorname{lca}_T(x,y')$ for every leaf $y'$ of color $\sigma(y)$. Every BMG has a unique *least resolved tree* (LRT), the explaining tree from which no inner edge can be contracted without changing the graph. For a vertex $u$ of $T$ the *support leaves* are $S_u=\operatorname{child}_T(u)\cap L$.

For a properly 2-colored digraph $(\mathcal{G},\sigma)$ on $L$, the *umbrella vertices* are

$$U(\mathcal{G},\sigma)=\{x\in L:\ N^+(x)=\{y\in L:\sigma(y)\ne\sigma(x)\}\},$$

the vertices pointing to every vertex of the other color. A *support set* is a maximal $S\subseteq U$ such that $x\in S$ implies $N^-(x)\subseteq S$. Every 2-colored digraph has a unique support set (the union of two such sets is again one), and it is the limit of the decreasing sequence $S^{(0)}=U$, $S^{(k)}=\{x\in S^{(k-1)}:N^-(x)\subseteq S^{(k-1)}\}$.

**Theorem.** Let $(T,\sigma)$ be the LRT of a 2-colored BMG $(\mathcal{G},\sigma)$ with root $\rho$. Then $S_\rho=S(\mathcal{G},\sigma)$. In particular $S(\mathcal{G},\sigma)\ne\emptyset$ if and only if $\mathcal{G}$ is connected.

**Corollary (recursion).** Each child of $\rho$ is either a support leaf in $S_\rho$ or the root of the LRT of a connected component of $\mathcal{G}-S_\rho$, and these components are exactly the BMGs $\mathcal{G}(T(v),\sigma|)$ for the inner children $v$ of $\rho$.

## Expansion

In the LRT of a 2-colored BMG an inner vertex $v\ne\rho$ has two colors below it, and since each subtree of the LRT explains a connected BMG, some child of $v$ carries a single color and is therefore a leaf. A leaf $x$ hanging directly from the root has the root as last common ancestor with every leaf of the other color, so it best-matches all of them and lies in $U$; any in-neighbor of $x$ must likewise reach $x$ at the root, so it is also attached to $\rho$, giving closure under in-neighbors. Conversely, a vertex deeper in the tree has an in-neighbor whose best matches stop below the root, which the iterated pruning removes.

## Sources

- D. Schaller, M. Geiß, M. Hellmuth, P. F. Stadler, "Least resolved trees for two-colored best match graphs", arXiv:2101.07000 (2021), Section 3 (Lemmas on support leaves, Definition of support leaves, Corollaries 2–3), Section 4 (umbrella vertices, support sets, Theorem 4), <https://doi.org/10.48550/arXiv.2101.07000>.

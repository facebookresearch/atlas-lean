# Subgraph swaps that preserve f-statistics

Let $G$ be an admixture graph: a finite directed acyclic graph with one root, in which every non-root node $v$ has parent edges $e$ with admixture proportions $\gamma_e\ge0$ summing to $1$ (a single parent edge with $\gamma_e=1$ at a tree node), and whose leaves are labelled populations. A [drift model](../patterson-s-f-statistics/drift-model.md) on $G$ assigns a root frequency $r$ and to every edge $e$ a square-integrable increment $\delta_e$ on a measure space $(\Omega,\mu)$, the increments mutually orthogonal with $\int\delta_e^2\,d\mu=\ell_e$, and node frequencies

$$p_{\mathrm{root}}=r,\qquad p_v=\sum_{e=(u\to v)}\gamma_e\,(p_u+\delta_e).$$

A *single-entry hybrid-closed subgraph* $A$ of $G$ is a set of nodes with a distinguished entry node $u\in A$ such that every parent of every node of $A\setminus\{u\}$ lies in $A$; its edges are the edges joining two nodes of $A$. Its boundary $\partial A$ consists of $u$ and the nodes of $A$ that are leaves or have an outgoing edge leaving $A$. For $a\in A$, induction along $A$ gives $p_a-p_u=\sum_{e\in E(A)}w_A(a,e)\,\delta_e$, where $w_A(a,e)$ is the total proportion of the paths from $u$ to $a$ through $e$. The *boundary covariance* of $A$ is

$$\Gamma_A(a,b)=\int(p_a-p_u)(p_b-p_u)\,d\mu=\sum_{e\in E(A)}w_A(a,e)\,w_A(b,e)\,\ell_e\qquad(a,b\in\partial A).$$

**Swap lemma.** Let $G_1$ and $G_2$ carry drift models that coincide outside single-entry hybrid-closed subgraphs $A_1\subseteq G_1$ and $A_2\subseteq G_2$ with the same entry node and the same boundary $\partial A$: the same nodes, edges, proportions and lengths outside $A_1$ and $A_2$, including the edges between $\partial A$ and the rest of the graph. If $\Gamma_{A_1}=\Gamma_{A_2}$ on $\partial A\times\partial A$, then the two models have the same [f2](../patterson-s-f-statistics/f2.md) at every pair of leaves. Hence they are [f-equivalent](f-equivalence-classes-of-drift-models.md): their centred leaf covariances and all f3 and f4 statistics agree.

**A 3-cycle instance.** Let $A_1$ have nodes $u,v,h$ and edges $u\to v$, $u\to h$, $v\to h$ of lengths $x,y,z$, where $h$ is an admixture node taking proportion $\gamma_1$ from $u$ and $\gamma_2=1-\gamma_1$ from $v$, and $v,h$ have edges leaving $A_1$ or are leaves. Let $A_2$ be the tree with nodes $u,w,v,h$ and edges $u\to w$, $w\to v$, $w\to h$ of lengths

$$s=\gamma_2x,\qquad a'=\gamma_1x,\qquad b'=\gamma_1^2y+\gamma_2^2z-\gamma_1\gamma_2x .$$

Both give $\Gamma(v,v)=x$, $\Gamma(v,h)=\gamma_2x$ and $\Gamma(h,h)=\gamma_1^2y+\gamma_2^2(x+z)$, so whenever $b'\ge0$ the graph with the 3-cycle and the graph with one fewer admixture node are f-equivalent. For example, $\gamma_1=\gamma_2=1/2$ and $x=y=z=1$ give the tree lengths $s=a'=1/2$ and $b'=1/4$. The pendant length $b'$ differs from Xu and Ané's average-distance adjustment $\gamma_1y+\gamma_2z$, because [f2 squares the lineage weights while the average distance does not](f2-drift-metric-versus-network-average-distance.md).

## Depends on

- [Admixture-graph drift model](../patterson-s-f-statistics/drift-model.md)
- [f2 statistic](../patterson-s-f-statistics/f2.md)
- [Which drift models have the f-statistics of a star tree](f-equivalence-classes-of-drift-models.md)

## Proof depends on

- [f2 in the drift model](../patterson-s-f-statistics/f2-freq.md)
- [f-statistics determine exactly the centred leaf covariance](f2-eq-iff-centred-cov-eq.md)
- [f2, independent-lineage distance and average network distance differ on admixture graphs](f2-drift-metric-versus-network-average-distance.md)

## Expansion

A proof writes every leaf frequency as $p_X=r+\sum_{e\notin E(A)}w(X,e)\,\delta_e+\sum_{a\in\partial A}\lambda(X,a)\,(p_a-p_u)$, where $\lambda(X,a)$ is the total proportion of the paths from $a$ to $X$ whose first edge leaves $A$. The coefficients $w(X,e)$ for $e\notin E(A)$ and $\lambda(X,a)$ are the same in both graphs, because the total proportion of the paths from $u$ to any $a\in A$ inside $A$ is $1$ in each graph. Orthogonality of the increments inside and outside $A$ then gives $f_2(X,Y)$ as a sum of a term outside $A$ and the quadratic form of $\Gamma_A$ in $(\lambda(X,\cdot)-\lambda(Y,\cdot))$. The page should also

- check the 3-cycle instance numerically, including the f2 matrices of a four-leaf example with leaves below $u$'s parent, $u$, $v$ and $h$;
- treat subgraphs with several entry nodes, the setting of Xu and Ané's swap lemma, where the boundary data must include the proportions of paths between boundary nodes.

## Sources

- J. Xu and C. Ané, *Identifiability of local and global features of phylogenetic networks from average distances*, arXiv:2110.11814v2 (2022), <https://arxiv.org/pdf/2110.11814>, Sec. 3.2, Lemma 15 (subgraph swap) and Proposition 6 (3-cycles), stated there for average distances. The transfer to f2 and the explicit pair above are derived here.

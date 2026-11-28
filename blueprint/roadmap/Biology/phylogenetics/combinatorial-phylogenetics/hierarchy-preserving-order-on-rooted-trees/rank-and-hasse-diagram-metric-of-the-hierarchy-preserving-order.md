# Rank and Hasse-diagram metric of the hierarchy-preserving order

**Setting.** On the poset $(RP(X),\le_{\rm HP})$ of rooted phylogenetic trees on $X$, $|X|=n$, let $d_{\rm HP}(T,T')$ be the graph distance between $T$ and $T'$ in the (undirected) Hasse diagram. For a tree $T$ with proper clusters $P(T)$ (clusters other than $X$ and singletons), define the rank

$$f(T)=\sum_{A\in P(T)}\bigl(|A|-1\bigr).$$

**Theorem.** Let $n\ge2$; items 4 and 5 assume $n\ge3$.

1. *(Local move)* $d_{\rm HP}(T,T')=1$ iff one tree is obtained from the other by replacing two distinct inclusion-maximal subclusters $A,B$ of a cluster $V$ by their union, i.e. $T'=T^V_{A\cup B}$ or $T=T'^V_{A\cup B}$.
2. *(Graded poset)* If $T\le_{\rm HP}T'$ then $d_{\rm HP}(T,T')=f(T')-f(T)$; in general $|f(T)-f(T')|\le d_{\rm HP}(T,T')\le f(T)+f(T')$.
3. *(Range of the rank)* $0\le f(T)\le\frac{(n-1)(n-2)}2$, with $0$ only for the star tree, the maximum attained by caterpillars, and every intermediate integer attained; so $\le_{\rm HP}$ is graded with rank function $f$.
4. *(Diameter, $n\ge3$)* $\frac{(n-1)(n-2)}2+1\le\Delta_{\rm HP}\le(n-1)(n-2)$.
5. *(Neighbourhoods, $n\ge3$)* A tree has at most $\binom n2$ up-neighbours, attained only by the star tree, and at most $2^{n-2}-1$ down-neighbours, attained only by trees whose single proper cluster is $X\setminus\{a\}$.
6. An upper bound $e_{\rm HP}(T,T')\ge d_{\rm HP}(T,T')$, obtained through common lower bounds built from a multi-hierarchy, is computable in polynomial time.

For $n=2$ there is only one hierarchy, $\{X,\{a\},\{b\}\}$, so $RP(X)$ is a single tree, $\Delta_{\rm HP}=0$, and the two-leaf star has no up- or down-neighbour; the bounds in items 4 and 5 fail there, and the lower-bound argument needs a tree with a proper two-leaf cluster, which exists only for $n\ge3$.

$d_{\rm HP}$ is a cluster-similarity metric: trees at small distance share most of their nesting structure, and the local move gives an explicit neighbourhood for MCMC proposals.

## Expansion

Each up-move $T\to T^V_{A\cup B}$ creates the cluster $A\cup B$ inside $V$ and raises $\sum(|A|-1)$ by exactly one, so every saturated chain between comparable trees has length $f(T')-f(T)$. Going from $T$ down to the star tree and up to $T'$ gives the upper bound $f(T)+f(T')$, and the caterpillar maximizes $f$, giving the diameter bounds.

## Depends on

- [Hierarchy-preserving partial order on rooted phylogenetic trees](hierarchy-preserving-partial-order-on-rooted-phylogenetic-trees.md)

## Sources

- Michael Hendriksen and Andrew Francis, "A partial order and cluster-similarity metric on rooted phylogenetic trees", arXiv:1906.02411 (2019), Sections 3–4, Theorems 3.1, 3.3, 3.5, 3.7 and 3.8, Corollaries 3.4 and 3.6, Proposition 4.10, <https://doi.org/10.48550/arXiv.1906.02411>.

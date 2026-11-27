# Symmetry nodes index versus cherry and Rogers J indices

For a rooted binary tree $T$ with $n$ leaves and $c(T)$ cherries, the **modified cherry index** is $\mathrm{mCI}(T)=n-2c(T)$ (leaves not in a cherry), and **Rogers' $J$ index** $J(T)$ counts the interior nodes whose two pendant subtrees have different numbers of leaves. Every non-symmetry node of a tree is either imbalanced or has equal-size but non-isomorphic subtrees, so $J(T)\le\mathrm{SNI}(T)$, and the [symmetry nodes index](extremal-values-of-the-symmetry-nodes-index.md) refines $J$ while generalizing the cherry count (parents of cherries are the simplest symmetry nodes).

**Theorems.**
1. For $n\ge2$, $\max\mathrm{mCI}=n-2$ and $\max J=n-2$, each attained uniquely by the caterpillar.
2. For $n\ge2$, $\min\mathrm{mCI}=n\bmod 2$, attained exactly by the *cherry trees* (all leaves in cherries except at most one). The number of minimizers is the Wedderburn–Etherington number $WE(n/2)$ for even $n$; for odd $n$ it is the $\tfrac{n-1}{2}$-th coefficient of $1/(1-g(z))$, where $g$ is the generating function of the Wedderburn–Etherington numbers, and this is less than $\tfrac{n+1}{2}WE(\tfrac{n+1}{2})$.
3. $\min J=wt(n)-1$, attained exactly by the rooted binary weight trees, the same minimizers as for $\mathrm{SNI}$.
4. Every $\mathrm{SNI}$-minimal (equivalently $J$-minimal) tree is $\mathrm{mCI}$-minimal.
5. If two trees with $n$ leaves are ranked in opposite orders by $\mathrm{SNI}$ and $J$, then $n\ge16$, and such pairs exist for every $n\ge16$.

So $\mathrm{SNI}$ and $J$ share their extremal trees, but $\mathrm{SNI}$ separates trees that $J$ cannot (equal-size, non-isomorphic subtrees), while $\mathrm{mCI}$ has many more minimizers.

## Depends on

- [Extremal values of the symmetry nodes index](extremal-values-of-the-symmetry-nodes-index.md)

## Expansion

A tree minimizing $\mathrm{mCI}$ only needs every leaf to sit in a cherry, so after contracting cherries any rooted binary tree on $\lfloor n/2\rfloor$ cherries (plus possibly one leaf) is admissible; counting unlabelled shapes gives Wedderburn–Etherington numbers. For $J$ the binary-carry argument used for $\mathrm{SNI}$ applies verbatim, because a node with equal-size subtrees costs nothing in $J$. A disagreement in ranking requires the two indices to trade imbalanced nodes against equal-size, non-isomorphic splits, which the paper shows is impossible below $16$ leaves; explicit constructions give such pairs for every $n\ge16$.

## Sources

- S. J. Kersting, M. Fischer, "Measuring tree balance using symmetry nodes -- a new balance index and its extremal properties", arXiv:2105.00719 (2021), Theorems 4.1, 4.3, 4.4, 5.1, 5.3, 5.4 and 6.1, <https://doi.org/10.48550/arXiv.2105.00719>.

# Second SPR neighbourhood depends on tree shape

**Setting.** Let $UB(n)$ be the set of unrooted binary phylogenetic trees with $n$ labelled leaves. A subtree prune and regraft (SPR) move cuts an edge, detaching a subtree, and reattaches it by subdividing an edge of the remaining tree; $\delta_{SPR}$ is the least number of such moves between two trees, and $N^2_{SPR}(T)=\{T':\delta_{SPR}(T,T')=2\}$. A tree is a *caterpillar* if its internal vertices induce a path, and *balanced* if all leaves are equidistant from a single vertex or edge. A *cherry* is a pair of leaves adjacent to a common vertex.

**Theorem.**

1. For every $T\in UB(n)$ with $n\ge3$, $|N^2_{SPR}(T)|\le 4(n-3)^2(2n-7)^2=O(n^4)$.
2. If $T$ is a caterpillar, $|N^2_{SPR}(T)|=\tfrac12 n^4+O(n^3)$; if $T$ is balanced, $|N^2_{SPR}(T)|=\tfrac13 n^4+O(n^3)$.
3. There are two families of trees with $n=3m$ leaves ($m\ge3$) and exactly three cherries, Type I and Type II, with

$$|N^2_{SPR}(T_1)|=\tfrac12 n^4+O(n^3)\quad(T_1\text{ of Type I}),\qquad |N^2_{SPR}(T_2)|=\tfrac{23}{54}n^4+O(n^3)\quad(T_2\text{ of Type II}).$$

Hence, unlike the Robinson–Foulds and NNI neighbourhoods, whose sizes at distance two are determined by $n$ and the number of cherries, the leading term of the second SPR neighbourhood depends on finer features of tree shape and is not a function of $(n,c)$ alone.

## Proof depends on

- [Asymptotic size of the k-th Robinson–Foulds and NNI neighbourhoods](asymptotic-size-of-the-k-th-robinson-foulds-and-nni-neighbourhoods.md)

## Expansion

The first SPR neighbourhood has the shape-independent size $2(n-3)(2n-7)$, which gives the upper bound in part 1. The leading $n^4$ term of the second neighbourhood comes from pairs of SPR moves acting on far-apart parts of the tree, which can be counted as ordered quadruples of edges lying along a path with pairwise separation at least three. The number of such quadruples depends on the counts $p_\ell(T)$ of paths of each length $\ell$ between edges, and these are not determined by $n$ and $c$ alone: caterpillars have many long paths, balanced trees few, which gives the different constants $1/2$ and $1/3$. The two three-cherry types differ in where their cherries sit, giving different path-length profiles with the same $(n,c)$.

## Sources

- Jamie V. de Jong, Jeanette C. McLeod, Mike Steel, "Neighbourhoods of phylogenetic trees: exact and asymptotic counts", arXiv:1508.03774 (2015): Section 6 (the two SPR theorems on caterpillars and balanced trees and on Type I and Type II three-cherry trees, and the corollary giving the general $O(n^4)$ bound), with path counts from the Appendix. <https://doi.org/10.48550/arXiv.1508.03774> Published version: SIAM Journal on Discrete Mathematics 30 (2016) 2265–2287, <https://doi.org/10.1137/15m1035070>.

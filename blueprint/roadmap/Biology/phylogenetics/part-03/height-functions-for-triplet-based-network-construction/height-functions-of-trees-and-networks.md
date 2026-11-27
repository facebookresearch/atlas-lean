# Height functions of rooted trees and networks

Let $X$ be a finite set and $\binom{X}{2}$ its 2-subsets. A **height function** on $X$ is any map $h: \binom{X}{2} \to \mathbb N$.

**Trees.** For a rooted tree $T$ with root $r$ and leaf set $X$, let $c_{ij}$ be the lowest common ancestor of leaves $i, j$, $d_T$ the path length and $l_T$ the length of a longest path from $r$. The height function of $T$ is

$$h_T(i, j) = l_T - d_T(r, c_{ij}).$$

A rooted triplet $ij|k$ is consistent with $T$ if and only if $h_T(i,j) < h_T(i,k)$ or $h_T(i,j) < h_T(j,k)$. Repeatedly deleting the maximum-weight edges of the complete graph on $X$ weighted by $h$ and recursing into components (HBUILD, analogous to BUILD) decides in polynomial time whether a tree with height function $h$ exists and reconstructs it.

**Networks.** For a rooted network $N$ (a rooted acyclic digraph with leaves labelled by $X$), let $d(r, u)$ be the length of a longest directed path from the root to $u$, $l_N$ the length of a longest root-to-leaf path, and $C_{ij}$ the set of lowest common ancestors of $i$ and $j$ (common ancestors with no common ancestor below them). Define

$$h_N(i, j) = \min\{\, l_N - d(r, c) : c \in C_{ij} \,\}.$$

**Theorem 2.** For distinct leaves $i, j, k$ of $N$, if $h_N(i,j) < h_N(i,k)$ or $h_N(i,j) < h_N(j,k)$, then the triplet $ij|k$ is consistent with $N$ (some displayed paths realize $ij|k$). The converse fails: there is a network consistent with $ij|k$ with $h(i,j) = h(i,k) = 3$ and $h(j,k) = 2$.

**Proposition 1.** For every height function $h$ on $X$ there is a (not necessarily binary) network $N$ with leaves labelled by $X$ such that $h_N = h + 1$. Distinct networks can share a height function, so $h_N$ is an intermediate summary rather than an encoding.

## Depends on

- [Rooted triplet](../../splits-compatibility-ultrametrics-and-upgma/triplet.md)

## Expansion

In a tree, $h_T(i,j) < h_T(i,k)$ means $c_{ij}$ lies strictly below $c_{ik}$, which is exactly the statement that $i, j$ form the cherry of the induced triplet. In a network, take a lowest common ancestor $v_{ij}$ realizing $h_N(i,j)$ with disjoint paths to $i$ and $j$, and a path to $k$ from a common ancestor $v_{ik}$ realizing $h_N(i,k)$; the strict inequality of heights prevents the path to $k$ from entering below $v_{ij}$, giving an embedded triplet $ij|k$. Proposition 1 hangs, for each pair with $h(i,j) < \max h$, a new node at depth $\max h - h(i,j)$ above copies of $i$ and $j$, and joins pairs with maximal $h$ directly through the root.

## Sources

- H. Poormohammadi, C. Eslahchi, R. Tusserkani, "TripNet: a method for constructing rooted phylogenetic networks from rooted triplets", PLoS ONE 9(9):e106531 (2014), Definitions 2, 3 and 5, Theorem 2, Proposition 1 and the HBUILD procedure, <https://doi.org/10.1371/journal.pone.0106531>, PMCID PMC4160195.
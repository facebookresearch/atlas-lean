# Parameterized complexity of graph, tree and path diets

**Problems.** *Graph-Diet*: given a graph $G$, a target treewidth $tw'$ and $d=tw-tw'$ where $tw$ is the treewidth of $G$, delete a minimum number of edges so that the remaining graph has treewidth at most $tw'$. *Tree-Diet* (resp. *Path-Diet*): given in addition a tree-decomposition (resp. path-decomposition) $\mathcal T$ of width $tw$, remove vertices from bags to reach width $tw'$ while losing the fewest edges (an edge is lost when no remaining bag contains both endpoints).

**Theorem.**

1. Graph-Diet admits no XP algorithm for the parameter $d$ unless $\mathrm P=\mathrm{NP}$.
2. Tree-Diet and Path-Diet are para-NP-hard for the target width $tw'$; they are NP-hard already for $tw'=1$.
3. Tree-Diet is para-NP-hard for $d$; it is W[1]-hard for the maximum degree $\Delta$ of $\mathcal T$ even when $d=1$.
4. Path-Diet is W[1]-hard for $d$.
5. Path-Diet is in XP for $d$: it can be solved in $O(tw^{2d}n)$ space and $O(tw^{4d}n)$ time.

## Expansion

(1) is a Turing reduction from computing treewidth: an oracle for Graph-Diet with $d=1$ and zero deleted edges, called for decreasing widths, finds the treewidth. (2) reduces from Spanning Caterpillar Tree via a path of $n-1$ full bags; the given decomposition is the extra constraint that makes $tw'=1$ hard, whereas Graph-Diet with $tw'=1$ is just spanning tree. (3) reduces from Multi-Colored Clique with one hub bag and $k$ children, and (4) from Clique on a $\delta$-regular graph with a single full bag: removing $k$ vertices loses exactly $\delta k-\binom k2$ edges if and only if they form a $k$-clique. (5) uses that on paths one may restrict to $d$-simple colorings, with at most $d$ red and $d$ orange vertices per bag, which bounds the number of table entries by a polynomial of degree $O(d)$ in $tw$. Together with the $2^{O(tw)}n$ algorithm for Tree-Diet, the source treewidth $tw$ is the parameter that makes the problem tractable.

## Depends on

- [Tree-diet problem and its coloring dynamic program](tree-diet-problem-and-its-coloring-dynamic-program.md)

## Sources

- B. Marchand, Y. Ponty, L. Bulteau, "Tree diet: reducing the treewidth to unlock FPT algorithms in RNA bioinformatics", *Algorithms for Molecular Biology* 17:8 (2022), Table 1, Theorems 2, 3, 4, 5 and 8, Proposition 2, <https://doi.org/10.1186/s13015-022-00213-z>, PMCID: PMC8976393.

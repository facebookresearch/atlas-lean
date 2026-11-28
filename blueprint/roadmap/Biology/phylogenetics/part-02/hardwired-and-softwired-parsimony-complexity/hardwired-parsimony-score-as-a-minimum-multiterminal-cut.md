# Hardwired parsimony score as a minimum multiterminal cut

Let $N$ be a phylogenetic network on a finite set $X$ (rooted: a directed acyclic graph with one root, no indegree-1 outdegree-1 nodes and leaves bijectively labelled by $X$; or unrooted: a connected undirected graph without degree-2 nodes and with leaves labelled by $X$). A $p$-state character is a map $\alpha: X \to \{1,\dots,p\}$; an extension $\tau$ of $\alpha$ assigns states to all nodes of $N$ agreeing with $\alpha$ on $X$. The **hardwired parsimony score** is

$$
PS_{\mathrm{hw}}(N,\alpha) = \min_{\tau} \sum_{(u,v) \in E(N)} \mathbf{1}[\tau(u) \neq \tau(v)],
$$

the minimum over extensions $\tau$ of the number of edges of $N$ whose endpoints receive different states.

Let $G$ be the undirected graph obtained from $N$ by merging, for each $i = 1,\dots,p$, all leaves $x$ with $\alpha(x) = i$ into a single terminal $\gamma_i$. A multiterminal cut of $(G,\{\gamma_1,\dots,\gamma_p\})$ is a set of edges whose removal places all terminals in different connected components. Then (Theorem 3.1)

$$
PS_{\mathrm{hw}}(N,\alpha) = \min\{|E'| : E' \text{ is a multiterminal cut of } (G,\{\gamma_1,\dots,\gamma_p\})\}.
$$

Consequences:

1. For a binary character ($p = 2$) the hardwired score is computable in polynomial time, as a minimum $s$-$t$ cut (Corollary 3.2).
2. For $p \ge 3$ computing the hardwired score is NP-hard and APX-hard, for rooted and unrooted networks alike (Corollary 3.3).
3. The hardwired score is fixed-parameter tractable in the score itself, and admits a polynomial-time $1.3438$-approximation for every $p$ and a $\tfrac{12}{11}$-approximation for $p = 3$ (Corollary 3.4).

When $N$ is a tree the hardwired score is the ordinary small-parsimony score.

## Depends on

- [Fitch's algorithm](../../small-parsimony-problem/fitch.md)

## Expansion

The edges changing state in an optimal extension separate any two terminals of different states, so they form a multiterminal cut; conversely, labelling every node by the state of the terminal in its component after removing a minimum cut (and any fixed state for components without a terminal) is an extension whose changes lie inside the cut. Hardness for $p \ge 3$ is the reverse reduction: from a multiterminal cut instance, replace each terminal by leaves of one state attached to its neighbours, suppress degree-2 nodes, and note that the score does not depend on edge orientation. The approximation ratios and the fixed-parameter algorithm are inherited from multiterminal cut and from multicut parameterized by cut size. The paper also shows that the extended Fitch heuristic previously proposed for rooted networks does not compute the hardwired score, even for binary characters on a three-leaf tree-child time-consistent network.

## Sources

- Mareike Fischer, Leo van Iersel, Steven Kelk, Celine Scornavacca, On computing the maximum parsimony score of a phylogenetic network, arXiv:1302.2430 (2013). <https://doi.org/10.48550/arXiv.1302.2430>. Published version: SIAM Journal on Discrete Mathematics 29(1) (2015), 559–585, <https://doi.org/10.1137/140959948>; locators above refer to the arXiv version.

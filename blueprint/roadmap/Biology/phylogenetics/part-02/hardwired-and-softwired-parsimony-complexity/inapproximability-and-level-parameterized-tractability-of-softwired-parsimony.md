# Inapproximability and level-parameterized tractability of softwired parsimony

Let $N$ be a rooted phylogenetic network on $X$ and $\alpha: X \to \{1,\dots,p\}$ a character. A rooted phylogenetic tree $T$ on $X$ is displayed by $N$ if it is obtained from a subgraph of $N$ by suppressing non-root nodes of total degree 2; $\mathcal{T}(N)$ is the set of displayed trees. The **softwired parsimony score** is

$$
PS_{\mathrm{sw}}(N,\alpha) = \min_{T \in \mathcal{T}(N)} \; \min_{\tau} \sum_{e \in E(T)} c_\tau(e),
$$

where $\tau$ ranges over extensions of $\alpha$ to $V(T)$ and $c_\tau(e) \in \{0,1\}$ indicates a state change on $e$. Equivalently, the minimum may be taken over switchings of $N$ (delete all but one incoming edge at every reticulation) and extensions of $\alpha$ to $V(N)$, counting changes on the edges of the switching (Lemma 4.5). A network is tree-child if every non-leaf node has a non-reticulation child, time-consistent if some time stamp $t: V(N) \to \mathbb{N}$ has $t(u) = t(v)$ on reticulation edges $(u,v)$ and $t(u) < t(v)$ on tree edges, and level-$k$ if every biconnected component has reticulation number at most $k$, with equality for at least one. Unless $\mathrm{P} = \mathrm{NP}$:

1. Computing $PS_{\mathrm{sw}}$ is NP-hard for a binary character on a binary rooted network (Theorem 4.2), and remains NP-hard on binary tree-child time-consistent networks (Theorem 4.3).
2. Deciding whether $PS_{\mathrm{sw}}(N,\alpha) = 1$ is NP-hard for binary characters on binary rooted time-consistent networks, so there is no algorithm fixed-parameter tractable in the parsimony score (Corollary 4.4).
3. For every constant $\epsilon > 0$ no polynomial-time algorithm approximates $PS_{\mathrm{sw}}$ within a factor $|X|^{1-\epsilon}$ on tree-child time-consistent networks with a binary character (Theorem 4.7), nor within a factor $|X|^{1/3-\epsilon}$ on rooted binary networks with a binary character (Theorem 4.8).

On the positive side, computing $PS_{\mathrm{sw}}(N,\alpha)$ for any number of states $p$ is fixed-parameter tractable in the level $k$ of $N$ (Theorem 5.7). The proof processes biconnected components bottom-up along the tree they form, running a weighted tree dynamic program of cost $O(p^2|V|)$ on each switching of a component (at most $2^k$ per component for binary networks), for a total of $O(2^k p^2 |V(N)|\,|E(N)|)$.

The softwired and hardwired scores coincide on trees, but on networks their difference is unbounded: there are binary tree-child time-consistent networks with $r$ reticulations and $3r+2$ leaves and a binary character with $PS_{\mathrm{sw}} = 2$ and $PS_{\mathrm{hw}} = r+1$.

## Depends on

- [Hardwired parsimony score as a minimum multiterminal cut](hardwired-parsimony-score-as-a-minimum-multiterminal-cut.md)

## Expansion

The hardness results reduce from cluster containment: after adding above the root an outgroup leaf in state 0, the character that is 1 exactly on a set $C$ has softwired score 1 if and only if the original network displays a tree with a subtree whose leaf set is $C$, and binary cluster containment is NP-hard (Lemma 4.1); separate reductions give the polynomial inapproximability bounds. The contrast with the hardwired score is structural: hardwired parsimony is a cut problem on a fixed graph, whereas softwired parsimony hides an exponential choice of displayed trees. The level algorithm exploits that every biconnected component has a unique root and that all incoming edges of a reticulation lie in one component, so switchings can be chosen independently per component and the optimal root-state costs of lower components passed up as node weights. The paper also gives integer linear programs that compute both scores exactly in practice.

## Sources

- Mareike Fischer, Leo van Iersel, Steven Kelk, Celine Scornavacca, On computing the maximum parsimony score of a phylogenetic network, arXiv:1302.2430 (2013). <https://doi.org/10.48550/arXiv.1302.2430>. Published version: SIAM Journal on Discrete Mathematics 29(1) (2015), 559–585, <https://doi.org/10.1137/140959948>; locators above refer to the arXiv version.

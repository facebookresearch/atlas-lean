# Consistency of maximum likelihood for the general Markov model on trees

Identifiability alone does not give consistency; Chang (1996, Theorem 5.1) proves it under stronger hypotheses than those of [full identifiability of the general Markov model](../../../not-yet-classified/general-markov-identifiability/identifiable-of-reconstructible-from-row.md) (Theorem 4.1).

Call a set $\mathcal{A}$ of $C \times C$ matrices strongly reconstructible from rows if for every $M \in \mathcal{A}$ and every permutation matrix $R \ne I$ the row-permuted matrix $RM$ does not lie in the closure $\overline{\mathcal{A}}$ of $\mathcal{A}$ in $\mathbb{R}^{C \times C}$. (Reconstructibility from rows, used in Theorem 4.1, only asks $RM \notin \mathcal{A}$.) Consider a class $\{P_\theta : \theta \in \Theta\}$ of Markov models on trees with a fixed set $T$ of terminal nodes, where $\theta$ consists of the topology, the marginal distribution at a specified node and the edge transition matrices, such that

1. every topology is bifurcating (nondegenerate), so that $\Theta$ is a subset of a single Euclidean space; a tree that merely has no nodes of degree $2$, such as the star on four leaves, is excluded;
2. for each model the marginal distribution at some node is positive at every state;
3. every edge transition matrix is invertible, is not a permutation matrix, and belongs to a fixed class $\mathcal{A}$ that is strongly reconstructible from rows.

Let $X^1, X^2, \ldots$ be i.i.d. copies of the vector of states at all nodes under $P_\theta$, and let $\hat\theta_n$ be a maximum likelihood estimate from the terminal-node states of $X^1, \ldots, X^n$. Then for every $\theta \in \Theta$, $P_\theta(\hat\theta_n \to \theta \text{ as } n \to \infty) = 1$: maximum likelihood recovers the topology and the edge transition matrices almost surely in the limit.

## Depends on

- [Full identifiability of the general Markov model](../../../not-yet-classified/general-markov-identifiability/identifiable-of-reconstructible-from-row.md)

## Expansion

1. The parameter space: bifurcating topologies on the fixed terminal set and transition matrices satisfying the three conditions, as a bounded but not closed subset of a Euclidean space, and its closure.
2. Strong reconstructibility from rows: the diagonal-largest-in-column class satisfies it, and a class that is reconstructible but not strongly reconstructible from rows.
3. The identifiability condition on the closure required by Lemma 5.1, derived from Theorem 4.1 and strong reconstructibility from rows.
4. Wald's consistency argument for a finite observation space (Chang, Lemma 5.1).
5. Degenerate (multifurcating) true topologies, with a metric identifying them with bifurcating models having identity matrices on some edges, as a separate statement.

## Sources

- J. T. Chang, Full reconstruction of Markov models on evolutionary trees: identifiability and consistency, Math. Biosci. 137 (1996), 51–73, Theorems 4.1 and 5.1. <https://doi.org/10.1016/s0025-5564(96)00075-2>

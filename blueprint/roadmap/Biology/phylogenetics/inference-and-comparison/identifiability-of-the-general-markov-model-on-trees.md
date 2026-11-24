# Identifiability of the general Markov model on trees

Consider a Markov model of character evolution on a tree with a finite state set $\mathcal{C}$, with a transition matrix $P^{rs}$ on each edge $\{r, s\}$, in which the joint distribution of states at the terminal nodes is observed. A class $\mathcal{A}$ of matrices is reconstructible from rows if for each $M \in \mathcal{A}$ and each permutation matrix $R \ne I$, $RM \notin \mathcal{A}$; for example, the matrices whose diagonal entry is the largest in its column ($P(j, j) > P(i, j)$ for $i \ne j$) form such a class. Chang (1996, Theorem 4.1) proves: if the tree has no nodes of degree $2$, some node $m$ has marginal distribution $\pi^m$ with $\pi^m(i) > 0$ for all states $i$, and every edge transition matrix is invertible, is not a permutation matrix and belongs to a fixed class reconstructible from rows, then the topology and all of the transition matrices are uniquely determined by the joint distribution of character states at the terminal nodes. The proof uses only joint distributions of triples of terminal nodes, identifying the rows of the transition matrices as eigenvectors of matrices formed from them (Section 4, identity (2)). His Theorem 5.1 deduces that maximum likelihood is consistent for the full model.

## Expansion

1. The model: the Markov model on a tree with edge transition matrices, and the hypotheses on degrees, marginals and transition matrices.
2. The definition of a class reconstructible from rows, the diagonal-largest-in-column example, and why permutation matrices must be excluded (relabelling of states at interior nodes).
3. The three-leaf case: the eigenvalue–eigenvector decomposition $(P^{ab})^{-1}P^{ab,y} = (P^{mb})^{-1}\mathrm{diag}(P^{\cdot c}_y)P^{mb}$, first when the relevant column has distinct entries, then in general.
4. The induction on the number of terminal nodes from a nonterminal node joined to at least two terminal nodes (Cases 1 and 2 of the proof).
5. Theorem 5.1: consistency of the maximum likelihood estimator via Wald's argument (Lemma 5.1), as a separate statement.

## Sources

- J. T. Chang, Full reconstruction of Markov models on evolutionary trees: identifiability and consistency, Math. Biosci. 137 (1996), 51–73, Theorems 4.1 and 5.1. <https://doi.org/10.1016/s0025-5564(96)00075-2>

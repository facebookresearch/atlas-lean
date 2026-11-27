# Displayed-tree parsimony is within a factor $k+1$ of softwired parsimony

Let $N$ be a rooted binary phylogenetic network on a leaf set $X$. Its level $k$ is the maximum number of reticulations (in-degree-two vertices) in a biconnected component, and $D(N)$ is its display set: the phylogenetic $X$-trees $T$ for which some subgraph of $N$ containing the root is a subdivision of $T$. For an alignment $A = (f_1,\dots,f_n)$ of characters $f_i : X \to C$, let $PS(A,T) = \sum_i PS(f_i,T)$ be the Fitch parsimony score on a tree $T$, and define the softwired parsimony scores

$$PS_{\mathrm{sw}}(A,N) = \sum_{i=1}^n \min_{T\in D(N)} PS(f_i,T), \qquad PS_{\mathrm{sw}'}(A,N) = \min_{T\in D(N)} \sum_{i=1}^n PS(f_i,T),$$

so that $PS_{\mathrm{sw}} \le PS_{\mathrm{sw}'}$. Then for **every** $T \in D(N)$,

$$PS(A,T) \le (k+1)\, PS_{\mathrm{sw}}(A,N) \qquad\text{and}\qquad PS(A,T) \le (k+1)\, PS_{\mathrm{sw}'}(A,N),$$

and the factor $k+1$ is sharp.

**Approximation.** For fixed $k$, computing any displayed tree of a level-$k$ network and running Fitch's algorithm on it is a polynomial-time $(k+1)$-approximation of both softwired parsimony scores, even though computing $PS_{\mathrm{sw}'}$ exactly is NP-hard already for level-$1$ networks and two binary characters ($PS_{\mathrm{sw}}$ is a sum of single-character scores, each fixed-parameter tractable in the level).

## Depends on

- [Fitch's algorithm computes the small-parsimony score](../../small-parsimony-problem/fitch-score-eq.md)
- [Softwired parsimony score of a phylogenetic network](../../displayed-tree-measures-on-phylogenetic-networks/softwired-parsimony-score-of-a-phylogenetic-network.md)

## Expansion

Two displayed trees whose switchings differ inside a single blob are related by a bounded number of rSPR moves, and an rSPR move changes the parsimony score of a character by at most its score. A blob is informative for a character only if the character changes state inside it, and non-informative blobs can be contracted. Comparing the given displayed tree with the optimal one blob by blob, each blob with $r \le k$ reticulations adds at most $k$ extra changes per unit of optimal score, which gives the factor $k+1$. Sharpness comes from explicit networks where every reticulation is forced to cost one extra change.

## Sources

- Janosch Döcker, Simone Linz and Kristina Wicke, "Bounding the Softwired Parsimony Score of a Phylogenetic Network", Bulletin of Mathematical Biology 86 (2024), 121, <https://doi.org/10.1007/s11538-024-01350-9>; numbering as in arXiv:2405.19587: Theorem 2.4, Corollary 2.5, Corollary 8.2 and Theorem 8.3.

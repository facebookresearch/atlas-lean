# Terminal-based fixed-parameter algorithm for the hybridization number

Let $T_1, T_2$ be rooted phylogenetic trees on taxon set $\mathcal X$, $|\mathcal X| = n$, not necessarily binary, with no nontrivial common pendant subtrees, and let $\mathcal C = Cl(T_1) \cup Cl(T_2)$ be their clusters. Let $r(\mathcal C)$ be the minimum number of reticulations of a rooted phylogenetic network representing all clusters of $\mathcal C$; it equals the hybridization number of $T_1,T_2$ (the minimum reticulation number of a network displaying binary refinements of both trees). For $Y \subseteq \mathcal X$, $\mathcal C \setminus Y$ is the cluster set restricted to $\mathcal X \setminus Y$.

For $x, y \in \mathcal X$ write $x \to_{\mathcal C} y$ if every non-singleton cluster of $\mathcal C$ containing $x$ also contains $y$. A taxon $x$ is a **terminal** if there is no $x' \ne x$ with $x \to_{\mathcal C} x'$.

**Theorem.** Suppose $r(\mathcal C) \ge 1$.

1. $\to_{\mathcal C}$ is a partial order whose maximal elements are the terminals, and every non-singleton cluster contains a terminal. A taxon $x$ is a terminal iff there are incompatible clusters $C_1, C_2 \in \mathcal C$ with $C_1 \cap C_2 = \{x\}$.
2. $\mathcal C$ has at most $3\,r(\mathcal C)$ terminals, and every set of at least $2r(\mathcal C)+1$ terminals contains a taxon $x$ with $r(\mathcal C \setminus \{x\}) < r(\mathcal C)$.
3. Let $\mathcal X'$ be any $2r(\mathcal C)+1$ terminals if there are more than $2r(\mathcal C)$ of them, and otherwise two taxa from each minimal cluster, at least one a terminal. Then $|\mathcal X'| \le 6\,r(\mathcal C)$ and some $x \in \mathcal X'$ satisfies $r(\mathcal C \setminus \{x\}) = r(\mathcal C) - 1$.
4. Consequently the hybridization number $r$ of two rooted, not necessarily binary trees can be computed, with an optimal network, in time $6^r\, r! \cdot \mathrm{poly}(n)$.

## Expansion

Deleting a single taxon lowers $r$ by at most one, and an optimal network yields an ordering of taxa (an ST-set tree sequence) whose successive removal lowers $r$ by one each time. In an optimal network every reticulation has a terminal below it, and a reticulation with no taxon of its own beneath it could be removed; counting the taxa that can sit directly below reticulations and the incompatible cluster pairs that create terminals gives the $3r$ bound. The algorithm branches on the at most $6r$ candidates of item 3, collapses common pendant subtrees after each deletion, recurses with parameter $r-1$, and reinserts the deleted taxa to rebuild the network, giving the $6^r r!$ search tree.

## Sources

- Teresa Piovesan, Steven Kelk, "A simple fixed parameter tractable algorithm for computing the hybridization number of two (not necessarily binary) trees", arXiv (2012); IEEE/ACM Transactions on Computational Biology and Bioinformatics (2013). Section 3 (Corollary 1), Section 4 (Observations 2–3, Corollary 2), Section 5 (Theorem 1), Section 6. <https://doi.org/10.48550/arXiv.1207.6090>. Published version: IEEE/ACM Transactions on Computational Biology and Bioinformatics 10(1) (2013), 18–25, <https://doi.org/10.1109/tcbb.2012.134>; locators above refer to the arXiv version.

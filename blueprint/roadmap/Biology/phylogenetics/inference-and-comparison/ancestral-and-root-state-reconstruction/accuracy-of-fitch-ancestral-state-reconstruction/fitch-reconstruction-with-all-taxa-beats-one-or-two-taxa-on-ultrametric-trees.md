# Fitch reconstruction with all taxa beats one or two taxa on ultrametric trees

**Setting.** $T$ is a rooted binary phylogenetic tree with root $\rho$ and leaf set $X$, *ultrametric* (equal expected number of substitutions from the root to every leaf). A character evolves under the symmetric $r$-state model $N_r$ on alphabet $\mathcal{A}$, $|\mathcal{A}| = r$: the root state is uniform on $\mathcal{A}$, and on each edge the probability $p_e$ of changing to any one specific other state is the same for all pairs of states, with $0\le p_e\le 1/r$ on every edge $e$. Let $p$ be the probability that a given leaf is in a specific state $\alpha$ different from the root state, so a single leaf shows the root state with probability $1 - (r-1)p$. The Fitch algorithm on the leaf data $f$ returns a set $\mathrm{MP}(f, T) \subseteq \mathcal{A}$ of most parsimonious root states; choosing uniformly from it gives the *reconstruction accuracy*

$$
RA(X) = \sum_{\alpha \in \mathcal{R} \subseteq \mathcal{A}} \frac{1}{|\mathcal{R}|}\, \mathbb{P}\big(\mathrm{MP}(f, T) = \mathcal{R} \mid \rho = \alpha\big).
$$

**Theorem.** For every rooted binary ultrametric tree:

1. *(Four states, $N_4$, DNA/RNA.)* $RA(X) \ge 1 - 3p$, so Fitch with all taxa is at least as accurate as reconstructing the root from any single taxon. Moreover, Fitch applied to any two taxa $x_1, x_2$ has $RA(\{x_1, x_2\}) = 1 - 3p$ (for $|X| = 2$, $RA(X) = 1 - 3p$), so all taxa also do at least as well as any pair.
2. *(Three states, $N_3$.)* $RA(X) \ge 1 - 2p$, and $RA(\{x_1, x_2\}) = 1 - 2p$ for any two taxa.

This settles, for $r = 3, 4$, the conjecture of Li, Steel and Zhang that on ultrametric trees under a symmetric model, using all terminal taxa is never worse than using one or two of them; the case $r = 2$ was known earlier.

## Depends on

- [Fitch's algorithm](../../../small-parsimony-problem/fitch.md)

## Expansion

For two leaves below the root, conditionally independent given $\rho$, Fitch returns the common state if they agree and both states otherwise. With $q = 1 - (r-1)p$, the root is recovered with weight $1$ when both leaves show it (probability $q^2$) and with weight $\tfrac12$ when exactly one does (probability $2q(r-1)p$), so $RA = q^2 + q(r-1)p = q$, the single-leaf value. The general case is an induction on the number of taxa: at the root the Fitch set is the intersection or union of the Fitch sets of the two maximal subtrees $Y_1, Y_2$, and one shows $D(X) = RA(X) - (1 - 3p) \ge 0$ from recursions for the probabilities of each possible root set in terms of the corresponding quantities for $Y_1$ and $Y_2$, using ultrametricity to relate their root-to-leaf change probabilities. The question matters because earlier studies found that, counterintuitively, adding taxa can decrease reconstruction accuracy.

## Sources

- L. Herbst, M. Fischer, "On the accuracy of ancestral sequence reconstruction for ultrametric trees with parsimony", arXiv:1706.06085 (2017): Section 2 (model $N_r$, Fitch algorithm, definition of $RA$), Section 3 (Theorem 1, Corollary 1, Proposition 1, Corollary 2 for $N_4$), Section 4 (Theorem 2, Corollary 3, Proposition 2, Corollary 4 for $N_3$). <https://doi.org/10.48550/arXiv.1706.06085> Published version: Bulletin of Mathematical Biology 80 (2018) 864–879, <https://doi.org/10.1007/s11538-018-0407-5>.

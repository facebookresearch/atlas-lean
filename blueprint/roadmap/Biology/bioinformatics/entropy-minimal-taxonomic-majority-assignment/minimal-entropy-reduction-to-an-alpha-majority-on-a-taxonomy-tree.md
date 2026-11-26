# Minimal-entropy reduction to an alpha-majority on a taxonomy tree

**Setting.** Let $T$ be a rooted taxonomy tree with node set $X$ and root $x^\ast$, write $a' \preceq a$ when $a'$ is an ancestor of (or equal to) $a$, and let $X_x$ be the node set of the subtree rooted at $x$. A contig has an annotation tuple $A = (a_1, \dots, a_N) \in X^N$; let $r_A(z)$ be the number of entries equal to $z$.

**Definitions.**

- For $\alpha \in (\tfrac12, 1]$, $A$ has an $\alpha$-majority if some taxon accounts for at least $\alpha N$ entries (it is then unique, and an $\alpha$-majority is also an $\alpha'$-majority for $\tfrac12 < \alpha' \le \alpha$).
- A reduction replaces entries by ancestors: $A' \preceq_r A$ if $a_k' \preceq a_k$ for every $k$. A consistent reduction collapses whole subtrees, so that no entry of the result is a strict ancestor of another; collapsing everything to the root always yields a $1$-majority.
- The entropy of $A$ is the Shannon entropy of its empirical distribution $p_A(z) = r_A(z)/N$:

$$H(A) = -\sum_{z} p_A(z) \log p_A(z) = \log N - \frac1N \sum_{z} r_A(z) \log r_A(z).$$

**Minimal-entropy reduction.** Find a reduction $A \to^\ast A'$ such that $A'$ has an $\alpha$-majority and $|H(A) - H(A')|$ is minimal, and assign the contig to the majority taxon of $A'$.

**Tree decomposition.** With $Y_x$ the children of $x$, $X_x = \{x\} \cup \bigcup_{y \in Y_x} X_y$, so the quantity to optimize, $\delta H(x; A') = -\sum_{z \in X_x} r_{A'}(z) \log r_{A'}(z)$, satisfies

$$\delta H(x; A') = -r_{A'}(x) \log r_{A'}(x) + \sum_{y \in Y_x} \delta H(y; A'),$$

which allows a single bottom-up pass over the tree.

**Proposition.** For every $A$ and $\alpha > \tfrac12$ there is a taxon $\hat x$ and a consistent reduction $A \to^\ast A''$ such that (i) $A''$ has an $\alpha$-majority, (ii) $A''$ minimizes the entropy change among all consistent reductions with that property, and (iii) $A''$ differs from $A$ only in entries that become $\hat x$; that is, an optimal reduction collapses exactly the annotations in one subtree onto its root.

## Expansion

Expanding $p \log p$ with $p = r/N$ and using $\sum_z r_A(z) = N$ gives the closed form of $H(A)$, and since $\log N$ and $H(A)$ are fixed, minimizing $|H(A) - H(A')|$ over reductions amounts to optimizing $\sum_z r_{A'}(z) \log r_{A'}(z)$, which splits over subtrees as above. For the proposition, the trivial collapse to the root shows feasible reductions exist, so an optimum exists; if $\tilde x$ is the $\alpha$-majority taxon of an optimal $A''$, then by consistency the same majority is achieved by collapsing only the annotations descending from $\tilde x$, which changes nothing else. Candidate subtrees are therefore the nodes $x$ with $\sum_{z \in X_x} r_A(z) \ge \alpha N$, and among those the algorithm picks the one whose collapse changes entropy least. This sits between the lowest common ancestor of all annotations (the root of the smallest subtree containing everything) and plurality voting; a likelihood-ratio test based on order statistics of multinomial counts then assesses whether the elected taxon is significantly supported.

## Sources

- N. W. Hanson, K. M. Konwar, S. J. Hallam, "LCA*: an entropy-based measure for taxonomic assignment within assembled metagenomes", Bioinformatics 32 (2016) 3535–3542, Section 2.1 (Definitions 1–3, Equation (1), Proposition 1), <https://doi.org/10.1093/bioinformatics/btw400> (PMC5181528).

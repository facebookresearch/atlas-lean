# Cartesian product decomposition of the ancestral configuration lattice

**Setting.** For a rooted binary labeled species tree $S$, let $C(S)$ be the lattice of root ancestral configurations of the matching gene tree–species tree pair and $D(S)$ its Hasse diagram, as in [the lattice of root ancestral configurations](root-ancestral-configurations-form-a-lattice-whose-maximal-chains-are-labeled-histories.md). For a digraph $D$ with maximal node $m$, let $\widehat D$ be $D$ with a new node $m'$ and an edge $m \to m'$ ($\widehat{\emptyset}$ is a single node). The Cartesian product $G \,\square\, H$ of digraphs has vertex set $V(G) \times V(H)$ and an edge $(u,v) \to (u',v')$ when $u = u'$ and $v \to v'$ in $H$, or $v = v'$ and $u \to u'$ in $G$. Write $D_1 \,\widehat\square\, D_2 = \widehat{D_1} \,\square\, \widehat{D_2}$.

**Theorem.** Let $S$ have $n \ge 2$ leaves, root children $r_\ell, r_r$ and root subtrees $S|_{r_\ell}$, $S|_{r_r}$. Then

$$D(S) \cong \widehat{D(S|_{r_\ell})} \,\square\, \widehat{D(S|_{r_r})}, \qquad\text{hence}\qquad c(S) = \big(c(S|_{r_\ell}) + 1\big)\big(c(S|_{r_r}) + 1\big).$$

Every such diagram is obtained from the empty graph and the one-node graph by repeated use of $\widehat\square$.

**Corollary (caterpillar subtree).** If the root subtrees are $S'$ with $|S'| \ge 1$ leaves and a caterpillar $\mathcal{C}_p$ with $p$ leaves, then the number $h$ of maximal chains (labeled histories) satisfies

$$h\big(D(S') \,\widehat\square\, D(\mathcal{C}_p)\big) = \binom{n+p-1}{p-1}\,h\big(D(S')\big), \qquad n = |S'| - 1.$$

**Non-matching pairs.** For a gene tree $G$ and species tree $S$ on the same leaf set, call two leaves of $G$ antipodal if they lie in different root subtrees of $S$. Then $C(G,S) \subseteq C(G,G)$, and $D(G,S)$ is the subgraph of $D(G,G)$ formed by all paths from the all-leaves configuration to the unique configuration in which exactly the non-antipodal pairs have coalesced. Consequently, for fixed $G$, the species trees maximizing $c(G,S)$ are exactly those with the same antipodal leaf pairs as $(G,G)$.

## Depends on

- [Root ancestral configurations form a lattice whose maximal chains are labeled histories](root-ancestral-configurations-form-a-lattice-whose-maximal-chains-are-labeled-histories.md)

## Expansion

Lineages from the two root subtrees never coalesce below the root of $S$, so a root configuration is a pair (configuration reaching the root from $S|_{r_\ell}$, configuration from $S|_{r_r}$). On each side the possible states are the root configurations of the subtree, plus one extra state in which that whole subtree has coalesced to the single lineage $r_\ell$ (or $r_r$); this is the appended node of $\widehat D$, and coalescence steps on the two sides commute, giving the Cartesian product. Counting vertices recovers the known recurrence for $c(S)$. Maximal chains of a product are shuffles of chains of the factors, and the caterpillar side is a single chain of length $p-1$, which gives the binomial factor.

## Sources

- Egor Lappo and Noah A. Rosenberg, "A lattice structure for ancestral configurations arising from the relationship between gene trees and species trees", *Discrete Applied Mathematics* 343 (2024), 65–81, <https://doi.org/10.1016/j.dam.2023.09.033>. Numbering as in the preprint arXiv:2111.10456v3, <https://arxiv.org/abs/2111.10456v3>: Definition 4, Theorem 6 and Proposition 7 (Section 7), Proposition 8 (Section 8), Definition 9, Proposition 10, Theorem 11 and Corollary 12 (Section 9).

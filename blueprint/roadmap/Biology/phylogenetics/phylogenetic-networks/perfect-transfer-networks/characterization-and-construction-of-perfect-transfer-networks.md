# Characterization and construction of perfect transfer networks

**Setting.** Let $\mathcal C$ be a set of binary characters (e.g. presence of a transposable element or organelle) and $\mathcal S$ a set of taxa, each taxon being the subset of characters it possesses. A *tree-based network* $G = (V, E_S \cup E_T)$ consists of a rooted base tree $\mathcal T_G$ with edges $E_S$ (vertical descent) plus transfer edges $E_T$ (horizontal gene transfer), with leaves mapped to taxa by $\sigma$. A $\mathcal C$-labeling $l$ assigns a character set to every node; $V_c(l)$ is the set of nodes carrying $c$ and $\overline V_c(l)$ its complement. $l$ *explains* $\mathcal S$ if $l(v)=\sigma(v)$ at every leaf; along every vertical (support) edge $(u,v)\in E_S$, $c\in l(u)$ implies $c\in l(v)$ (a character is never lost once acquired); and for each $c\in\mathcal C$ a unique node of $V_c(l)$ reaches every node of $V_c(l)$ in $G[V_c(l)]$ (a single origin). Transfer edges may pass any subset of characters. $G$ is a *perfect transfer network* (PTN) for $\mathcal S$ if some labeling explains $\mathcal S$.

**Theorem.**

1. *(Characterization.)* A labeling $l$ of a tree-based network explains $\mathcal S$ if and only if (i) $l(v) = \sigma(v)$ at every leaf; (ii) for each $c \in \mathcal C$, the subgraph induced by $V_c(l)$ is connected and has a unique node of in-degree $0$; and (iii) for each $c$, either $V_c(l) = V$ or the base tree restricted to $\overline V_c(l)$ is connected and contains the root.
2. *(Recognition.)* Whether a given tree-based network is a PTN for $\mathcal S$ can be decided in $O(|\mathcal C|\,|V(G)|^2)$ time.
3. *(Completion bounds.)* For a base tree $T$ with leaf map $\sigma$, let $A_c$ be the set of first-appearance nodes of $c$ in the Fitch labeling. Every PTN with base tree $T$ needs at least $\max_c(|A_c| - 1)$ transfer edges, and a greedy completion algorithm, running in $O(|\mathcal C|^2|\mathcal S| + |\mathcal C||\mathcal S|^2)$ time from the Fitch pre-labeling, adds at most $\sum_c(|A_c| - 1)$ transfer edges; it is thus a $|\mathcal C|$-approximation.
4. PTNs are incomparable with ancestral recombination graphs with a bounded number of recombinations $d$, but every PTN-explainable set is ARG-explainable with unboundedly many recombinations.

## Expansion

Unique birth means each character's carriers form a connected region of the network rooted at the birth node, reached through vertical and transfer edges; rarity of loss means that the non-carriers must form a connected region of the base tree containing the root, i.e. the character was absent ancestrally and lost only by vertical descent away from it. These convexity conditions can be checked per character in polynomial time. In a fixed base tree each extra first-appearance of a character in the Fitch parsimony labeling must be bridged by at least one transfer, giving the lower bound; one transfer per extra appearance suffices.

## Sources

- Alitzel López Sánchez and Manuel Lafond, "Predicting horizontal gene transfers with perfect transfer networks", Algorithms for Molecular Biology 19 (2024), 6, <https://doi.org/10.1186/s13015-023-00242-2>; numbering as in arXiv:2312.02962: Theorems 1, 2, 3, Propositions 1, 2 and Corollary 1.

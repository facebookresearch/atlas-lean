# Jukes–Cantor mixtures of contracted trees mimic the resolved tree

Use the mixture-model notation $\mathcal M_{\mathcal T}, \mathcal M^{+}_{\mathcal T}, \mathcal M^{++}_{\mathcal T}$ and the notions of weak, strong and complete mimicking for phylogenetic site-pattern distributions, now under the Jukes–Cantor (JC) or Kimura 2-parameter (K2P) submodels.

**Theorem (linear invariant).** Let $T_1 = T_{12|34}$, $T_2 = T_{13|24}$, $T_3 = T_{14|23}$, and in Fourier (Hadamard) coordinates $q$ put $l(q) = q_{GGGG} - q_{GGTT}$. Under JC and K2P: $l(q) = 0$ on $\mathcal M_{T_1}$; $l(q) \ge 0$ on $\mathcal M_{T_2}$ and $\mathcal M_{T_3}$, with $l(q) > 0$ on their open models; and $l(q) = 0$ on $\mathcal M_{T_i}$ ($i = 2,3$) forces a zero internal branch. Consequently, if $\mathcal S$ consists of copies of a tree $T_1$ on taxa $X$ and $\mathcal M_{\mathcal S}\cap\mathcal M^{++}_{\mathcal T} \ne \emptyset$ for some multiset $\mathcal T$, then for every four-taxon subset $K$ and every $T \in \mathcal T$ the restriction $T|_K$ is either a star or equals $T_1|_K$, i.e. every tree of $\mathcal T$ is refined by $T_1$. If moreover all trees of $\mathcal T$ are binary and $T_1 \notin \mathcal T$, then $\mathcal M_{\mathcal S}\cap\mathcal M^{+}_{\mathcal T} = \emptyset$.

**Theorem (complete mimicking).** Let $T$ be a tree with an internal vertex $v$ adjacent to $u_1, u_2, u_3$, and let $T_i$ be obtained by contracting the edge $u_iv$ ($i = 1,2$). Under JC, the two-class mixture $\mathcal M^{*}_{\{T_1,T_2\}}$ completely mimics $\mathcal M^{*}_{\{T\}}$.

So a mixture of two less-resolved trees can reproduce every JC distribution of the resolved tree exactly, while mixtures cannot imitate a genuinely different resolved topology.

## Expansion

The group-based structure of JC and K2P diagonalizes the transition matrices in Fourier coordinates, with parameters satisfying $a_A = 1$ and the multiplicative inequalities $a_C \ge a_Ga_T$ etc. (Proposition 3). The coordinates $q_{GGGG}$ and $q_{GGTT}$ are products of edge parameters that coincide on $T_{12|34}$ and differ by a factor determined by the internal edge on the other quartets, giving the sign of $l$. For complete mimicking, JC distributions on $T$ and on the contracted trees $T_1, T_2$ are compared in the same Fourier coordinates, where each coordinate of a mixture is the weighted average of the corresponding edge-parameter products; the paper exhibits mixing weights and edge parameters on $T_1$ and $T_2$ reproducing every JC distribution on $T$.

## Depends on

- [Few-class mixtures on one tree cannot mimic another tree](few-class-mixtures-on-one-tree-cannot-mimic-another-tree.md)

## Sources

- Elizabeth S. Allman, John A. Rhodes, Seth Sullivant, "When do phylogenetic mixture models mimic other phylogenetic models?", arXiv (2012). Section "Results" (Theorems 3 and 4), Appendix (Propositions 3 and 4). <https://doi.org/10.48550/arXiv.1202.2396>. Published version: Systematic Biology 61(6) (2012), 1049–1059, <https://doi.org/10.1093/sysbio/sys064>; locators above refer to the arXiv version.

# Species-Reaction Graph criteria for concordant reaction networks

**Concordance.** For a reaction network with species $\mathscr{S}$, reactions $y \to y'$ and stoichiometric subspace $S = \mathrm{span}\{y' - y\}$, let $L \colon \mathbb{R}^{\mathscr{R}} \to S$, $L\alpha = \sum_{y \to y'} \alpha_{y \to y'}(y' - y)$. The network is *concordant* if there do not exist $\alpha \in \ker L$ and a nonzero $\sigma \in S$ such that
1. for each reaction with $\alpha_{y \to y'} \ne 0$, $\mathrm{supp}\, y$ contains a species $s$ with $\mathrm{sgn}\,\sigma_s = \mathrm{sgn}\,\alpha_{y \to y'}$;
2. for each reaction with $\alpha_{y \to y'} = 0$, either $\sigma_s = 0$ for all $s \in \mathrm{supp}\,y$, or $\mathrm{supp}\,y$ contains $s, s'$ with $\mathrm{sgn}\,\sigma_s = -\mathrm{sgn}\,\sigma_{s'} \ne 0$.

A network is *fully open* if every species has a degradation reaction $s \to 0$. A kinetics $\mathscr{K}$ is *weakly monotonic* if, whenever both compositions contain $\mathrm{supp}\,y$, $\mathscr{K}_{y\to y'}(c^{**}) > \mathscr{K}_{y \to y'}(c^*)$ forces $c^{**}_s > c^*_s$ for some $s \in \mathrm{supp}\,y$, and equality of rates forces either $c^{**} = c^*$ on $\mathrm{supp}\,y$ or two reactant species moving in opposite directions (mass action is weakly monotonic).

**Species-Reaction (SR) Graph.** The bipartite graph with species and reaction vertices, an edge between $s$ and $y \to y'$ when $s$ occurs in $y$ or $y'$, labeled by that complex and its stoichiometric coefficient (degradation and synthesis reactions omitted). A *c-pair* is a pair of edges at a common reaction vertex carrying the same complex label; a cycle is *even* if it contains an even number of c-pairs. For a cycle $s_1 - R_1 - s_2 - \dots - s_n - R_n - s_1$ traversed in a fixed direction, with $f_{R_i \to s_{i+1}}$ and $e_{s_i \to R_i}$ the coefficients on the edges, it is an *s-cycle* if

$$\frac{f_{R_1 \to s_2} f_{R_2 \to s_3} \cdots f_{R_n \to s_1}}{e_{s_1 \to R_1} e_{s_2 \to R_2} \cdots e_{s_n \to R_n}} = 1.$$

Two cycles have a *species-to-reaction intersection* if their intersection is nonempty and every connected component of it is a path with a species at one end and a reaction at the other.

**Theorem.** If in the SR Graph of a fully open network (i) every even cycle is an s-cycle and (ii) no two even cycles have a species-to-reaction intersection, then the network is concordant, and in fact strongly concordant. The conclusion extends to every *nondegenerate* network with these SR Graph properties (all weakly reversible networks included), and then:
1. for every weakly monotonic kinetics, each positive equilibrium is the only equilibrium, positive or boundary, in its stoichiometric compatibility class;
2. if the network is weakly reversible, then for any kinetics no nontrivial compatibility class has a boundary equilibrium; if it is also conservative, every continuous weakly monotonic kinetics has exactly one equilibrium in each nontrivial class, and it is positive;
3. for differentiably monotonic kinetics every positive equilibrium is nondegenerate and every real eigenvalue of its Jacobian (restricted to $S$) is negative.

## Expansion

Concordance is a sign condition on the stoichiometry alone: it says that no direction $\sigma$ in the stoichiometric subspace can be reconciled with a flux perturbation $\alpha \in \ker L$ consistent with monotone kinetics. Discordance would produce a "sign-causality" graph that must contain a directed cycle; the SR Graph conditions force every such cycle to be an even cycle with balanced stoichiometry and keep even cycles from interlocking, which rules this out. Because the test reads off a finite graph, it certifies uniqueness and stability of equilibria for whole classes of kinetics without knowing rate constants.

## Sources

- Guy Shinar and Martin Feinberg, "Concordant chemical reaction networks and the Species-Reaction Graph", Mathematical Biosciences 241 (2013), 1–23, <https://doi.org/10.1016/j.mbs.2012.08.002>; numbering as in arXiv:1203.6560: Definition 4.1, Definitions 3.10–3.11, Theorem 2.1, Corollary 2.4, Theorem 2.6 and Theorem 2.8 and Section 1 (SR Graph, c-pairs, s-cycles).

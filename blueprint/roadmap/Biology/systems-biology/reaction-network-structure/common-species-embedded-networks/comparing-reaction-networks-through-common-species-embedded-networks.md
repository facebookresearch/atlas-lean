# Comparing reaction networks through common-species embedded networks

**Setting.** For a chemical reaction network $\mathscr{N}$ with species set $\mathscr{S}$ and a subset $\mathscr{S}' \subseteq \mathscr{S}$, the *embedded network* $\mathscr{N}|_{\mathscr{S}'}$ is obtained by deleting all species outside $\mathscr{S}'$ from every complex and then discarding trivial reactions (those whose reactant and product become equal) and duplicates. Two kinetic systems $(\mathscr{N}, K)$ and $(\mathscr{N}^*, K^*)$ are *dynamically equivalent* if they define the same species-formation rate function, and *proximately equivalent* if there are kinetics $\widetilde K$, $\widetilde K^*$ differing from $K$, $K^*$ at most in their inflow reactions ($0 \to X$) such that $(\mathscr{N}, \widetilde K)$ and $(\mathscr{N}^*, \widetilde K^*)$ are dynamically equivalent.

**Method (CSEN analysis).** Given two models $\mathscr{N}$, $\mathscr{N}^*$ of the same biological system:
1. form the embedded networks $\mathscr{N}_E$, $\mathscr{N}^*_E$ with respect to the common species $\mathscr{S}' = \mathscr{S}_{\mathscr{N}} \cap \mathscr{S}_{\mathscr{N}^*}$;
2. split the reactions of each embedded network into reactions common to the original networks, reactions that become common only after embedding, and non-common reactions;
3. look for a (maximal) proximate transformation mapping the non-common reactions of $\mathscr{N}_E$ onto those of $\mathscr{N}^*_E$ (a network operation or dynamical equivalence), and measure similarity by how many reactions it fixes.

**Theorem (Wnt signaling models).**
1. The embedded networks of the Lee (mono-stationary) and Feinberg (multi-stationary) Wnt models with respect to their common species are dynamically equivalent under mass action, except for one inflow reaction, via an $S$-extending network operation; hence they are proximately equivalent.
2. The mass-action embedded Schmitz network transforms into the MacLean embedded subnetwork without the outflows $A_4 \to 0$, $A_5 \to 0$, a generalized mass-action system that is mass action in $14$ of $19$ reactions, and the transformation is the identity on $11$ of the $15$ Schmitz reactions.

So the mono- versus multi-stationary distinction between Lee and Feinberg is carried by species outside the common core, while Feinberg and MacLean admit no comparable correspondence.

## Depends on

- [Chemical reaction network](../../../../Dynamics/smooth-dynamics/reaction-network.md)

## Expansion

Embedding is the network analogue of projecting onto shared coordinates: it keeps exactly the reactions visible through the common species, so differences in auxiliary intermediates disappear. Dynamical equivalence on the embedded networks then means that the two models induce the same vector field on the common species up to inflow terms, which can be absorbed by adjusting production rates. Counting fixed versus transformed reactions gives a quantitative notion of how close two published models are.

## Sources

- B. S. Hernandez, P. V. N. Lubenia and E. R. Mendoza, "Embedding-based comparison of reaction networks of Wnt signaling", *Match Communications in Mathematical and in Computer Chemistry* 93(1) (2024), 235–245, Section 3 (CSEN method and proximate equivalence), Theorems 4.1 and 5.2, <https://doi.org/10.46793/match.93-1.223h> (preprint arXiv:2404.06515).

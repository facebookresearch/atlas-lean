# Siphon criterion for persistence of reaction networks

Consider a chemical reaction network whose reaction rates $R_j$ satisfy the hypotheses of Angeli, De Leenheer and Sontag: each $R_j$ is real-analytic on an open set containing the closed nonnegative orthant, depends only on the concentrations of its reactants, is nondecreasing in each reactant concentration and constant in the others (their condition (5)), and is zero exactly when the concentration of some reactant is zero (mass action included); and consider its associated Petri net. A siphon is a nonempty set of species $Z$ such that every reaction producing a species of $Z$ consumes a species of $Z$ (Definition 3.3 of the source); a P-semiflow is a nonzero nonnegative vector $c$ of species weights with $c^{T}\Gamma = 0$ for the stoichiometric matrix $\Gamma$, that is, a nonzero nonnegative conservation law, and its support is the set of species $i$ with $c_i > 0$ (Definition 3.1). Both nondegeneracy conditions matter: the zero vector has empty support, contained in every set, and with it the test below would pass for the conservative network $A \to B$, in which $A(t) \to 0$; with the definitions above, $\{A\}$ is a siphon containing the support of no P-semiflow, since the only conservation laws are the multiples of $A + B$. Angeli, De Leenheer and Sontag (2007, Theorem 2) prove: if the Petri net is conservative and every siphon contains the support of a P-semiflow, then the network is persistent, that is, no trajectory starting in the positive orthant has an $\omega$-limit point on its boundary. Their Theorem 1 gives a converse-type statement: a conservative and persistent network has a consistent associated Petri net.

## Depends on

- [Is Siphon](../../not-yet-classified/siphon-prime-decomposition/is-siphon.md)

## Expansion

1. The model: reaction networks, the kinetics hypothesis, the associated Petri net, nonempty siphons, nonzero P-semiflows and the definitions of conservativity and persistence.
2. The key lemma that the set of species vanishing at an $\omega$-limit point on the boundary is a siphon.
3. Theorem 2: a siphon containing the support of a P-semiflow cannot be emptied, which excludes boundary $\omega$-limit points.
4. Theorem 1: consistency of the Petri net for conservative persistent networks, via an interior $\omega$-limit argument.
5. Examples from enzymatic reactions and phosphorylation cycles, as in the source.

## Sources

- D. Angeli, P. De Leenheer and E. D. Sontag, A Petri net approach to the study of persistence in chemical reaction networks, Math. Biosci. 210 (2007), 598–618, Theorems 1 and 2. <https://arxiv.org/abs/q-bio/0608019>

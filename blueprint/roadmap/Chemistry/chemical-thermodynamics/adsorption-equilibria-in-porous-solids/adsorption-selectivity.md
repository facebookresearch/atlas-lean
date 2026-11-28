# Adsorption selectivity

The adsorption selectivity of component $i$ over $j$ is the ratio of their adsorbed loadings divided by the ratio of their bulk fugacities (or bulk mole fractions).

For a mixture in equilibrium with an adsorbent, with adsorbed molar loadings $q_i, q_j > 0$, bulk partial fugacities
$f_i, f_j > 0$ and bulk mole fractions $y_i, y_j > 0$, the fugacity-normalized and composition-normalized adsorption
selectivities are

$$
S^{f}_{ads,ij} = \frac{q_i/q_j}{f_i/f_j}, \qquad S^{y}_{ads,ij} = \frac{q_i/q_j}{y_i/y_j} .
$$

They are equal when $f_i/f_j = y_i/y_j$, for example for an ideal-gas bulk or when the two components have equal
fugacity coefficients; in a real mixture they can differ. A selectivity above $1$ means that $i$ is enriched relative to
$j$ in the adsorbed phase, not necessarily that its adsorbed mole fraction exceeds its bulk mole fraction. In either
convention $S_{ads,ji} = 1/S_{ads,ij}$.

## Context

Graduate level. Selectivity at fixed composition is the headline separation metric reported for porous frameworks.

## Depends on

None.

## Proof depends on

None.

## Expansion

The selectivity depends in general on composition and total pressure; in the fugacity convention it is constant for
competitive Langmuir adsorption with equal capacities.

## Sources

- R. Krishna and J. M. van Baten, "How Reliable Is the Ideal Adsorbed Solution Theory for the Estimation of Mixture Separation Selectivities in Microporous Crystalline Adsorbents?", *ACS Omega* 6, 15499–15513 (2021), [doi.org](https://doi.org/10.1021/acsomega.1c02136), Eqn (1).

# Apparent equilibrium constant and transformed reaction Gibbs energy

A biochemical reaction is written between reactants, each a sum of species, and balances every element except those whose free ions the medium keeps fixed. Its standard transformed reaction Gibbs energy defines the apparent equilibrium constant; the transformed reaction Gibbs energy at actual concentrations is a different quantity.

**Setting.** Fix $T>0$, $P$, $I$, pH and pMg. Let $I'$ be a finite set of reactants. Each non-water reactant $i$ is a [pseudoisomer group](standard-transformed-gibbs-energy-of-a-reactant.md) with standard transformed Gibbs energy $\Delta_fG_i'^\circ$, concentration $[\mathrm B_i]>0$ and $\Delta_fG_i'=\Delta_fG_i'^\circ+RT\ln[\mathrm B_i]$. All species of a group contain the same numbers of atoms of each element other than hydrogen and magnesium, so the composition matrix $A'$ of the reactants over these elements is well defined. Solvent water may be a reactant; in the pure-solvent convention its transformed Gibbs energy of formation is $\Delta_fG'^\circ(\mathrm{H_2O})$, with no concentration term.

**Definition.** A biochemical reaction is a vector $\nu'\in\mathbb R^{I'}$, positive on products and negative on reactants, that is [balanced](../../amounts-and-stoichiometry/balanced-reactions-and-stoichiometric-conservati/is-balanced.md) for $A'$: $A'\nu'=0$. It does not impose balance of hydrogen, magnesium or electric charge. Its standard transformed reaction Gibbs energy, apparent equilibrium constant, biochemical reaction quotient and transformed reaction Gibbs energy are

$$
\Delta_rG'^\circ=\sum_{i\in I'}\nu_i'\,\Delta_fG_i'^\circ,\qquad K'=\exp\Bigl(-\frac{\Delta_rG'^\circ}{RT}\Bigr),
$$

$$
Q'=\prod_{i\in I'\setminus\{\mathrm{H_2O}\}}[\mathrm B_i]^{\nu_i'},\qquad \Delta_rG'=\sum_{i\in I'}\nu_i'\,\Delta_fG_i'.
$$

Water contributes to $\Delta_rG'^\circ$ and $\Delta_rG'$ but contributes no factor to $Q'$, and $K'$ is the value of $Q'$ at equilibrium.

**Properties.**

1. $\Delta_rG'=\Delta_rG'^\circ+RT\ln Q'$, and $K'>0$.
2. $\Delta_rG'=0$ exactly when $Q'=K'$, the biochemical equilibrium condition, and $\Delta_rG'<0$ exactly when $Q'<K'$.
3. Replacing $\nu'$ by $c\nu'$ with $c>0$ multiplies $\Delta_rG'^\circ$ and $\Delta_rG'$ by $c$ and replaces $K'$ by $K'^{\,c}$; reversing the reaction inverts $K'$. A value of $K'$ is meaningful only with the written reaction.
4. $\Delta_rG'$ and $\Delta_rG'^\circ$ coincide only when $Q'=1$. The same $\Delta_rG'^\circ<0$ is compatible with $\Delta_rG'>0$ at concentrations with $Q'>K'$, so $\Delta_rG'^\circ$ alone does not fix the direction of a reaction in a given solution.
5. $\Delta_rG'^\circ$ and $K'$ are functions of $T$, $I$, pH and pMg through the species data, not constants attached to the reactants.

## Depends on

- [Standard transformed Gibbs energy of a pseudoisomer group](standard-transformed-gibbs-energy-of-a-reactant.md)
- [Balanced reaction for a composition matrix](../../amounts-and-stoichiometry/balanced-reactions-and-stoichiometric-conservati/is-balanced.md)

## Proof depends on

- [Standard transformed Gibbs energy of a pseudoisomer group](standard-transformed-gibbs-energy-of-a-reactant.md)

## Expansion

Property 1 substitutes $\Delta_fG_i'=\Delta_fG_i'^\circ+RT\ln[\mathrm B_i]$ for each non-water reactant and $\Delta_fG'^\circ(\mathrm{H_2O})$ for water. Property 2 follows because $RT>0$ and $\ln$ is strictly increasing: $\Delta_rG'=RT\ln(Q'/K')$. Property 3 is linearity in $\nu'$. Property 4 rereads property 2. The sign of $\Delta_rG'$ is the quantity the source uses for the direction of a biochemical reaction at specified concentrations.

## Sources

- R. A. Alberty, A. Cornish-Bowden, R. N. Goldberg, G. G. Hammes, K. Tipton and H. V. Westerhoff, *Recommendations for terminology and databases for biochemical thermodynamics*, IUBMB Recommendations, Biophysical Chemistry 155 (2011) 89–103, <https://doi.org/10.1016/j.bpc.2011.03.007>. Equation numbers are those of the official IUBMB-hosted author manuscript (August 2010, 53 pages), <https://iubmb.qmul.ac.uk/thermod2/BiochemThermodynamics.pdf>: Section 2, equations (2-5)–(2-7) and the discussion of water; Section 7, equations (7-1), (7-7)–(7-10); Section 8, equation (8-10).

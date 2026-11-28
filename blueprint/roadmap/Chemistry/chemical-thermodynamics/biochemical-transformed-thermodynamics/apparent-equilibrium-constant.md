# Apparent equilibrium constant and transformed reaction Gibbs energy

A biochemical reaction is written between reactants, each a sum of species, and has an underlying chemical equation balanced in atoms and charge once the medium's hydrogen and magnesium ions are added. Its standard transformed reaction Gibbs energy defines the apparent equilibrium constant; the transformed reaction Gibbs energy at actual concentrations is a different quantity.

**Setting.** Fix $T>0$, $P$, $I$, pH and pMg. Let $I'$ be a finite set of reactants. Each non-water reactant $i$ is a [pseudoisomer group](standard-transformed-gibbs-energy-of-a-reactant.md) $J_i$ with standard transformed Gibbs energy $\Delta_fG_i'^\circ$, concentration $[\mathrm B_i]>0$ and $\Delta_fG_i'=\Delta_fG_i'^\circ+RT\ln[\mathrm B_i]$. All species of a group contain the same numbers of atoms of each element other than hydrogen and magnesium, so the composition matrix $A'$ of the reactants over these elements is well defined, and since they interconvert by binding hydrogen and magnesium ions, $c_i=z_j-N_{\mathrm H}(j)-2N_{\mathrm{Mg}}(j)$ is the same for every $j\in J_i$, with $z_j$ the charge number. Solvent water may be a reactant, a single species with $c=-2$; in the pure-solvent convention its transformed Gibbs energy of formation is $\Delta_fG'^\circ(\mathrm{H_2O})$, with no concentration term.

**Formal quantities.** For any vector $\nu'\in\mathbb R^{I'}$, positive on products and negative on reactants, define the standard transformed reaction Gibbs energy, the apparent equilibrium constant, the biochemical reaction quotient and the transformed reaction Gibbs energy

$$
\Delta_rG'^\circ=\sum_{i\in I'}\nu_i'\,\Delta_fG_i'^\circ,\qquad K'=\exp\Bigl(-\frac{\Delta_rG'^\circ}{RT}\Bigr),
$$

$$
Q'=\prod_{i\in I'\setminus\{\mathrm{H_2O}\}}[\mathrm B_i]^{\nu_i'},\qquad \Delta_rG'=\sum_{i\in I'}\nu_i'\,\Delta_fG_i'.
$$

Water contributes no activity factor to $Q'$ or $K'$, while its standard transformed formation energy contributes to $\Delta_rG'^\circ$ and $\Delta_rG'$.

**Definition (biochemical reaction).** A vector $\nu'$ is a biochemical reaction when it has an underlying chemical equation: for some choice of species $j(i)\in J_i$ there are $n_{\mathrm H},n_{\mathrm{Mg}}\in\mathbb R$ such that $\sum_i\nu_i'\mathrm B_{j(i)}+n_{\mathrm H}\mathrm{H^+}+n_{\mathrm{Mg}}\mathrm{Mg^{2+}}=0$ balances every element and electric charge. No other species, and in particular no electrons, may be added. Equivalently, $\nu'$ is [balanced](../../amounts-and-stoichiometry/balanced-reactions-and-stoichiometric-conservati/is-balanced.md) for $A'$, $A'\nu'=0$, and $\sum_i\nu_i'c_i=0$; the choice of the $j(i)$ does not matter. The biochemical equation itself, written between reactants, need not balance hydrogen, magnesium or charge. $A'\nu'=0$ alone is necessary but not sufficient: for single-species groups $\mathrm{Fe^{3+}}$ and $\mathrm{Fe^{2+}}$, the vector of $\mathrm{Fe^{3+}}\to\mathrm{Fe^{2+}}$ satisfies $A'\nu'=0$ but has $\sum_i\nu_i'c_i=-1$, since this half reaction needs an electron.

**Properties.** Properties 1 and 3 hold for every vector; properties 2 and 4 give the physical reading for a biochemical reaction that the system carries out.

1. $\Delta_rG'=\Delta_rG'^\circ+RT\ln Q'$, and $K'>0$.
2. $\Delta_rG'=0$ exactly when $Q'=K'$, and $\Delta_rG'<0$ exactly when $Q'<K'$. For a biochemical reaction that the system carries out, $Q'=K'$ is its equilibrium condition, so $K'$ is the value of $Q'$ at equilibrium.
3. Replacing $\nu'$ by $c\nu'$ with $c>0$ multiplies $\Delta_rG'^\circ$ and $\Delta_rG'$ by $c$ and replaces $K'$ by $K'^{\,c}$; reversing the reaction inverts $K'$. A value of $K'$ is meaningful only with the written reaction.
4. $\Delta_rG'$ and $\Delta_rG'^\circ$ coincide only when $Q'=1$. The same $\Delta_rG'^\circ<0$ is compatible with $\Delta_rG'>0$ at concentrations with $Q'>K'$, so $\Delta_rG'^\circ$ alone does not fix the direction of a biochemical reaction in a given solution.
5. $\Delta_rG'^\circ$ and $K'$ are functions of $T$, $I$, pH and pMg through the species data, not constants attached to the reactants.

## Depends on

- [Standard transformed Gibbs energy of a pseudoisomer group](standard-transformed-gibbs-energy-of-a-reactant.md)
- [Balanced reaction for a composition matrix](../../amounts-and-stoichiometry/balanced-reactions-and-stoichiometric-conservati/is-balanced.md)

## Proof depends on

- [Standard transformed Gibbs energy of a pseudoisomer group](standard-transformed-gibbs-energy-of-a-reactant.md)

## Expansion

Property 1 substitutes $\Delta_fG_i'=\Delta_fG_i'^\circ+RT\ln[\mathrm B_i]$ for each non-water reactant and $\Delta_fG'^\circ(\mathrm{H_2O})$ for water. Property 2 follows because $RT>0$ and $\ln$ is strictly increasing: $\Delta_rG'=RT\ln(Q'/K')$. Property 3 is linearity in $\nu'$. Property 4 rereads property 2. The sign of $\Delta_rG'$ is the quantity the source uses for the direction of a biochemical reaction at specified concentrations.

For the equivalence in the definition: hydrogen and magnesium balance force $n_{\mathrm H}=-\sum_i\nu_i'N_{\mathrm H}(j(i))$ and $n_{\mathrm{Mg}}=-\sum_i\nu_i'N_{\mathrm{Mg}}(j(i))$, the other elements balance exactly when $A'\nu'=0$, and the charge of the completed equation is $\sum_i\nu_i'z_{j(i)}+n_{\mathrm H}+2n_{\mathrm{Mg}}=\sum_i\nu_i'c_i$. Since $c_i$ does not depend on the species chosen, neither does the condition. For example, $\mathrm{ATP}+\mathrm{H_2O}=\mathrm{ADP}+\text{phosphate}$ is a biochemical reaction, with $c=-16,-2,-15,-3$ from $\mathrm{ATP^{4-}}$ ($\mathrm{C_{10}H_{12}N_5O_{13}P_3^{4-}}$), water, $\mathrm{ADP^{3-}}$ ($\mathrm{C_{10}H_{12}N_5O_{10}P_2^{3-}}$) and $\mathrm{HPO_4^{2-}}$, summing with the signs of $\nu'$ to $0$. Combining twice the iron half reaction with the reverse of the hydrogen half reaction gives $2\,\mathrm{Fe^{3+}}+\mathrm{H_2}=2\,\mathrm{Fe^{2+}}$, in which the electrons cancel and $\sum_i\nu_i'c_i=-6-(-2)+4=0$.

## Sources

- R. A. Alberty, A. Cornish-Bowden, R. N. Goldberg, G. G. Hammes, K. Tipton and H. V. Westerhoff, *Recommendations for terminology and databases for biochemical thermodynamics*, IUBMB Recommendations, Biophysical Chemistry 155 (2011) 89–103, <https://doi.org/10.1016/j.bpc.2011.03.007>. Equation numbers are those of the official IUBMB-hosted author manuscript (August 2010, 53 pages), <https://iubmb.qmul.ac.uk/thermod2/BiochemThermodynamics.pdf>: Section 2, equations (2-5)–(2-7) and the discussion of water; Section 7, equations (7-1), (7-7)–(7-10); Section 8, equation (8-10); Section 9, p. 33, that half reactions do not balance charge, that the electrons of the two half reactions of an oxidoreductase reaction must cancel, and the hydrogen half reaction (9-2).

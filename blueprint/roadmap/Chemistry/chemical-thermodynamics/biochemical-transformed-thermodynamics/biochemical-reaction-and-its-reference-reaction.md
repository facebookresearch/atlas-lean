# Apparent and chemical equilibrium constants of ATP hydrolysis

For ATP hydrolysis at specified pH without magnesium, the apparent equilibrium constant of $\mathrm{ATP}+\mathrm{H_2O}=\mathrm{ADP}+\text{phosphate}$ equals the chemical equilibrium constant of the reference reaction $\mathrm{ATP^{4-}}+\mathrm{H_2O}=\mathrm{ADP^{3-}}+\mathrm{HPO_4^{2-}}+\mathrm{H^+}$ times $10^{\mathrm{pH}}$ times an explicit ratio of species fractions.

**Setting.** Consider an aqueous solution at specified $T>0$, $P$, ionic strength $I$ and pH that contains no magnesium, so that pMg plays no role. As biochemical reactants, ATP is the equilibrium mixture of its hydrogen-ion species ($\mathrm{ATP^{4-}}$, $\mathrm{HATP^{3-}}$ and $\mathrm{H_2ATP^{2-}}$ in the middle pH range), ADP the mixture of its hydrogen-ion species, including $\mathrm{ADP^{3-}}$, and phosphate the mixture of its hydrogen-ion species, including $\mathrm{HPO_4^{2-}}$. Concentrations are divided by $c^\circ=1\ \mathrm{mol\,L^{-1}}$, a reactant's concentration is the sum of the concentrations of its species, and $\mathrm{pH}=-\log_{10}[\mathrm{H^+}]$ uses the concentration of the hydrogen ion. Water is the solvent, with the pure-solvent standard state, and enters neither constant. Suppose the solution is at equilibrium: the hydrolysis and every hydrogen-ion dissociation among the species are at equilibrium, all concentrations are positive, and the pH is the equilibrium value. Let

$$
r(\mathrm{ATP^{4-}})=\frac{[\mathrm{ATP^{4-}}]}{[\mathrm{ATP}]},\qquad r(\mathrm{ADP^{3-}})=\frac{[\mathrm{ADP^{3-}}]}{[\mathrm{ADP}]},\qquad r(\mathrm{HPO_4^{2-}})=\frac{[\mathrm{HPO_4^{2-}}]}{[\text{phosphate}]}
$$

be the equilibrium mole fractions of these species in their [pseudoisomer groups](standard-transformed-gibbs-energy-of-a-reactant.md). The chemical equilibrium constant of the reference reaction and the [apparent equilibrium constant](apparent-equilibrium-constant.md) of the biochemical reaction are the equilibrium values

$$
K=\frac{[\mathrm{ADP^{3-}}]\,[\mathrm{HPO_4^{2-}}]\,[\mathrm{H^+}]}{[\mathrm{ATP^{4-}}]},\qquad K'=\frac{[\mathrm{ADP}]\,[\text{phosphate}]}{[\mathrm{ATP}]}.
$$

The reference reaction is [balanced](../../amounts-and-stoichiometry/balanced-reactions-and-stoichiometric-conservati/is-balanced.md) in every element and in charge; the biochemical reaction balances every element except hydrogen, and not charge.

**Theorem.** Then

$$
K'=K\;10^{\,\mathrm{pH}}\;\frac{r(\mathrm{ATP^{4-}})}{r(\mathrm{ADP^{3-}})\,r(\mathrm{HPO_4^{2-}})}.
$$

Consequently:

1. $\log_{10}K'=\log_{10}K+\mathrm{pH}+\log_{10}r(\mathrm{ATP^{4-}})-\log_{10}r(\mathrm{ADP^{3-}})-\log_{10}r(\mathrm{HPO_4^{2-}})$. The factor $10^{\mathrm{pH}}$ comes from the single hydrogen ion the reference reaction produces, and the fractions bring in the acid dissociation of the three reactants.
2. With the fractions given by the species energies as on the pseudoisomer-group page, they depend only on $T$, $I$ and pH, so $K'$ is a function of $T$, $I$ and pH, while $K$ depends only on $T$ and $I$.
3. In energy form, with $\Delta_rG^\circ=-RT\ln K$ for the reference reaction and $\Delta_rG'^\circ=-RT\ln K'$,

$$
\Delta_rG'^\circ=\Delta_rG^\circ-RT\ln(10)\,\mathrm{pH}-RT\ln\frac{r(\mathrm{ATP^{4-}})}{r(\mathrm{ADP^{3-}})\,r(\mathrm{HPO_4^{2-}})}.
$$

## Derived extensions

These statements generalize the theorem. They are not printed in the source, and each is proved here.

**General reference reaction.** Let $\nu'$ be any biochemical reaction at specified pH, with pMg not specified, whose non-water reactants are pseudoisomer groups $J_i$ differing only in hydrogen count, with fractions $r_j=\exp((\Delta_fG_i'^\circ-\Delta_fG_j'^\circ)/RT)$ built from the [species energies](standard-transformed-gibbs-energy-of-a-species.md) (water is a one-species group with $r=1$). Choose representatives $j(i)\in J_i$, let $n_{\mathrm H}=-\sum_i\nu_i'N_{\mathrm H}(j(i))$, and let $\Delta_rG^\circ_{\mathrm{ref}}=\sum_i\nu_i'\Delta_fG^\circ_{j(i)}+n_{\mathrm H}\Delta_fG^\circ(\mathrm{H^+})$ and $K_{\mathrm{ref}}=\exp(-\Delta_rG^\circ_{\mathrm{ref}}/RT)$ for the reference reaction $\sum_i\nu_i'\mathrm B_{j(i)}+n_{\mathrm H}\mathrm{H^+}=0$. Then

$$
K'=K_{\mathrm{ref}}\;10^{\,n_{\mathrm H}\mathrm{pH}}\prod_ir_{j(i)}^{-\nu_i'}.
$$

*Proof.* By the definition of the species energies, $\sum_i\nu_i'\Delta_fG'^\circ_{j(i)}=\Delta_rG^\circ_{\mathrm{ref}}-n_{\mathrm H}RT\ln(10)\,\mathrm{pH}$. The fraction formula gives $\Delta_fG_i'^\circ=\Delta_fG'^\circ_{j(i)}+RT\ln r_{j(i)}$. Sum with weights $\nu_i'$, divide by $-RT$ and exponentiate.

**Equal reaction Gibbs energies.** In that setting, at pseudoisomer equilibrium with concentrations $[\mathrm B_j]>0$, $\Delta_rG_{\mathrm{ref}}=\sum_i\nu_i'(\Delta_fG^\circ_{j(i)}+RT\ln[\mathrm B_{j(i)}])+n_{\mathrm H}\mu(\mathrm{H^+})$ equals $\Delta_rG'$. *Proof.* Substituting $n_{\mathrm H}$ gives $\sum_i\nu_i'\Delta_fG'_{j(i)}$, and pseudoisomer equilibrium gives $\Delta_fG'_{j(i)}=\Delta_fG_i'$.

**Choice of representatives.** $K'$ does not depend on the representatives, while $K_{\mathrm{ref}}$, $n_{\mathrm H}$ and the product of fractions in general do. This makes precise the source's remark that the reference reaction is arbitrary and $n$ has no mechanistic significance. *Proof.* $K'$ is defined from $\Delta_rG'^\circ$ alone, and two representatives of one group with different hydrogen counts give different $n_{\mathrm H}$.

**Magnesium factor.** If pMg is also specified and the species energies carry the magnesium terms of the species page's derived extension, add $n_{\mathrm{Mg}}=-\sum_i\nu_i'N_{\mathrm{Mg}}(j(i))$ magnesium ions to the reference reaction and $n_{\mathrm{Mg}}\Delta_fG^\circ(\mathrm{Mg^{2+}})$ to $\Delta_rG^\circ_{\mathrm{ref}}$. Then $K'=K_{\mathrm{ref}}\,10^{\,n_{\mathrm H}\mathrm{pH}+n_{\mathrm{Mg}}\mathrm{pMg}}\prod_ir_{j(i)}^{-\nu_i'}$. *Proof.* The proof of the general identity, with the magnesium term carried along.

## Depends on

- [Apparent equilibrium constant and transformed reaction Gibbs energy](apparent-equilibrium-constant.md)
- [Standard transformed Gibbs energy of a pseudoisomer group](standard-transformed-gibbs-energy-of-a-reactant.md)
- [Standard transformed Gibbs energy of formation of a species](standard-transformed-gibbs-energy-of-a-species.md)
- [Balanced reaction for a composition matrix](../../amounts-and-stoichiometry/balanced-reactions-and-stoichiometric-conservati/is-balanced.md)

## Proof depends on

- [Apparent equilibrium constant and transformed reaction Gibbs energy](apparent-equilibrium-constant.md)
- [Standard transformed Gibbs energy of a pseudoisomer group](standard-transformed-gibbs-energy-of-a-reactant.md)
- [Standard transformed Gibbs energy of formation of a species](standard-transformed-gibbs-energy-of-a-species.md)
- [Balanced reaction for a composition matrix](../../amounts-and-stoichiometry/balanced-reactions-and-stoichiometric-conservati/is-balanced.md)

## Expansion

Substitute $[\mathrm{ATP^{4-}}]=r(\mathrm{ATP^{4-}})[\mathrm{ATP}]$, $[\mathrm{ADP^{3-}}]=r(\mathrm{ADP^{3-}})[\mathrm{ADP}]$ and $[\mathrm{HPO_4^{2-}}]=r(\mathrm{HPO_4^{2-}})[\text{phosphate}]$ into $K$:

$$
K=\frac{r(\mathrm{ADP^{3-}})\,r(\mathrm{HPO_4^{2-}})}{r(\mathrm{ATP^{4-}})}\,K'\,[\mathrm{H^+}],
$$

and $[\mathrm{H^+}]=10^{-\mathrm{pH}}$. All quantities are positive, so the identity can be solved for $K'$, and consequence 1 takes $\log_{10}$. Consequence 2 uses the fraction formula of the pseudoisomer-group page, whose standard transformed energies depend on $T$, $I$ and pH. Consequence 3 takes $-RT\ln$ of the theorem. Element balance of the reference reaction uses the formulas $\mathrm{C_{10}H_{12}N_5O_{13}P_3^{4-}}$, $\mathrm{C_{10}H_{12}N_5O_{10}P_2^{3-}}$, $\mathrm{HPO_4^{2-}}$ and $\mathrm{H_2O}$.

## Sources

- R. A. Alberty, A. Cornish-Bowden, R. N. Goldberg, G. G. Hammes, K. Tipton and H. V. Westerhoff, *Recommendations for terminology and databases for biochemical thermodynamics*, IUBMB Recommendations, Biophysical Chemistry 155 (2011) 89–103, <https://doi.org/10.1016/j.bpc.2011.03.007>. Equation numbers are those of the official IUBMB-hosted author manuscript (August 2010, 53 pages), <https://iubmb.qmul.ac.uk/thermod2/BiochemThermodynamics.pdf>: Section 2, equations (2-3)–(2-7), with the species of ATP, the water convention, the standard concentration and the measurement of pH at equilibrium, for the theorem; Section 4, equation (4-12); Section 6, equations (6-3) and (6-8); Section 7, equations (7-9) and (7-11), with the remarks that $f(\mathrm{pH})$ brings in the pKs and that $n$ has no mechanistic significance, for the derived extensions.

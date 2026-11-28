# Biochemical reaction and its chemical reference reaction

Choosing one species from each reactant and adding hydrogen ions to balance them turns a biochemical reaction at specified pH into a chemical reference reaction. The apparent equilibrium constant is then the reference constant times $10^{n\,\mathrm{pH}}$, with $n$ the hydrogen ions the reference reaction produces, times an explicit product of species fractions.

**Setting.** Use the setting of the [apparent equilibrium constant](apparent-equilibrium-constant.md) at specified $T>0$, $P$, $I$ and pH, with pMg not specified: each non-water reactant $i\in I'$ is a [pseudoisomer group](standard-transformed-gibbs-energy-of-a-reactant.md) $J_i$ whose species differ only in their numbers of hydrogen atoms, with standard transformed energy $\Delta_fG_i'^\circ$ and equilibrium mole fractions

$$
r_j=\exp\Bigl(\frac{\Delta_fG_i'^\circ-\Delta_fG_j'^\circ}{RT}\Bigr)\qquad(j\in J_i),
$$

where $\Delta_fG_j'^\circ$ are the [standard transformed Gibbs energies of formation of the species](standard-transformed-gibbs-energy-of-a-species.md). Solvent water is a one-species group with $r=1$ and no concentration term. Let $\nu'$ be a biochemical reaction, $A'\nu'=0$. Choose one representative species $j(i)\in J_i$ for each reactant and let

$$
n_{\mathrm H}=-\sum_{i\in I'}\nu_i'\,N_{\mathrm H}(j(i)).
$$

The reference reaction $\sum_i\nu_i'\mathrm B_{j(i)}+n_{\mathrm H}\mathrm{H^+}=0$ balances every element, and $n_{\mathrm H}$ is the number of hydrogen ions it produces (negative when it consumes them). Its standard reaction Gibbs energy and chemical equilibrium constant, in the source's ionic-strength convention, are

$$
\Delta_rG^\circ_{\mathrm{ref}}=\sum_i\nu_i'\,\Delta_fG^\circ_{j(i)}+n_{\mathrm H}\,\Delta_fG^\circ(\mathrm{H^+}),\qquad K_{\mathrm{ref}}=\exp\Bigl(-\frac{\Delta_rG^\circ_{\mathrm{ref}}}{RT}\Bigr).
$$

**Statement.** The apparent equilibrium constant $K'=\exp(-\Delta_rG'^\circ/RT)$ satisfies

$$
K'=K_{\mathrm{ref}}\;10^{\,n_{\mathrm H}\mathrm{pH}}\,f(\mathrm{pH}),\qquad f(\mathrm{pH})=\prod_{i\in I'}r_{j(i)}^{-\nu_i'},
$$

where $f$ depends on pH only through the fractions of the chosen species, which the species data fix. This is the source's relation $K'=K_{\mathrm{ref}}10^{n\mathrm{pH}}f(\mathrm{pH})$. The source describes $f$ only as bringing in the acid dissociation constants of the reactants; the statement identifies it exactly.

For example, for $\mathrm{ATP}+\mathrm{H_2O}=\mathrm{ADP}+\text{phosphate}$ the representatives $\mathrm{ATP^{4-}}$, $\mathrm{H_2O}$, $\mathrm{ADP^{3-}}$, $\mathrm{HPO_4^{2-}}$ give the reference reaction $\mathrm{ATP^{4-}}+\mathrm{H_2O}=\mathrm{ADP^{3-}}+\mathrm{HPO_4^{2-}}+\mathrm{H^+}$, $n_{\mathrm H}=1$ and

$$
K'=K_{\mathrm{ref}}\;10^{\,\mathrm{pH}}\,\frac{r(\mathrm{ATP^{4-}})}{r(\mathrm{ADP^{3-}})\,r(\mathrm{HPO_4^{2-}})}.
$$

## Derived extensions

These statements are not printed in the source; each is proved here.

**Equal reaction Gibbs energies at pseudoisomer equilibrium.** If every group is at pseudoisomer equilibrium at concentrations $[\mathrm B_j]>0$, then $\Delta_rG_{\mathrm{ref}}=\sum_i\nu_i'(\Delta_fG_{j(i)}^\circ+RT\ln[\mathrm B_{j(i)}])+n_{\mathrm H}\,\mu(\mathrm{H^+})$ equals the transformed reaction Gibbs energy $\Delta_rG'$. *Proof.* Substituting $n_{\mathrm H}$ gives $\Delta_rG_{\mathrm{ref}}=\sum_i\nu_i'\,\Delta_fG'_{j(i)}$, and pseudoisomer equilibrium gives $\Delta_fG'_{j(i)}=\Delta_fG_i'$.

**Choice of representatives.** $K'$ does not depend on the representatives, while $K_{\mathrm{ref}}$, $n_{\mathrm H}$ and $f$ in general do: two representatives of one group with different hydrogen counts give different $n_{\mathrm H}$. *Proof.* $K'$ is defined from $\Delta_rG'^\circ$ alone. This is the precise form of the source's remark that the reference reaction is arbitrary and $n$ has no mechanistic significance.

**Magnesium factor.** If pMg is also specified and the species energies carry the magnesium terms of the species page's derived extension, set $n_{\mathrm{Mg}}=-\sum_i\nu_i'N_{\mathrm{Mg}}(j(i))$ and add $n_{\mathrm{Mg}}\mathrm{Mg^{2+}}$ to the reference reaction and $n_{\mathrm{Mg}}\Delta_fG^\circ(\mathrm{Mg^{2+}})$ to $\Delta_rG^\circ_{\mathrm{ref}}$. Then $K'=K_{\mathrm{ref}}\,10^{\,n_{\mathrm H}\mathrm{pH}+n_{\mathrm{Mg}}\mathrm{pMg}}\prod_ir_{j(i)}^{-\nu_i'}$. *Proof.* The main proof with the magnesium term carried along.

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

Element balance: species of a group share all element counts except that of hydrogen, so $A'\nu'=0$ balances the other elements, and $n_{\mathrm H}$ balances hydrogen. By the definition of the species energies, $\Delta_fG'^\circ_{j(i)}=\Delta_fG^\circ_{j(i)}-N_{\mathrm H}(j(i))\{\Delta_fG^\circ(\mathrm{H^+})-RT\ln(10)\,\mathrm{pH}\}$, so

$$
\sum_i\nu_i'\,\Delta_fG'^\circ_{j(i)}=\Delta_rG^\circ_{\mathrm{ref}}-n_{\mathrm H}RT\ln(10)\,\mathrm{pH}.
$$

The fraction formula gives $\Delta_fG_i'^\circ=\Delta_fG'^\circ_{j(i)}+RT\ln r_{j(i)}$, hence $\Delta_rG'^\circ=\sum_i\nu_i'\Delta_fG_i'^\circ=\Delta_rG^\circ_{\mathrm{ref}}-n_{\mathrm H}RT\ln(10)\,\mathrm{pH}+RT\sum_i\nu_i'\ln r_{j(i)}$. Dividing by $-RT$ and exponentiating gives the statement. Water contributes $\Delta_fG'^\circ(\mathrm{H_2O})$ to both sides of the first identity and $r=1$ to $f$.

## Sources

- R. A. Alberty, A. Cornish-Bowden, R. N. Goldberg, G. G. Hammes, K. Tipton and H. V. Westerhoff, *Recommendations for terminology and databases for biochemical thermodynamics*, IUBMB Recommendations, Biophysical Chemistry 155 (2011) 89–103, <https://doi.org/10.1016/j.bpc.2011.03.007>. Equation numbers are those of the official IUBMB-hosted author manuscript (August 2010, 53 pages), <https://iubmb.qmul.ac.uk/thermod2/BiochemThermodynamics.pdf>: Section 2, equations (2-3)–(2-6) for the ATP reference reaction and constants; Section 4, equation (4-12); Section 6, equations (6-3) and (6-8); Section 7, equation (7-9), and equation (7-11) with the statements that $f(\mathrm{pH})$ brings in the pKs and that $n$ has no mechanistic significance.

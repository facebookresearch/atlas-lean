# Biochemical reaction and its chemical reference reaction

Choosing one species from each reactant and adding hydrogen and magnesium ions to balance them turns a biochemical reaction into a chemical reference reaction. At pseudoisomer equilibrium the two have the same reaction Gibbs energy, and the apparent equilibrium constant is the reference constant times a pH and pMg factor.

**Setting.** Use the setting of the [apparent equilibrium constant](apparent-equilibrium-constant.md): reactants $i\in I'$ are pseudoisomer groups $J_i$ satisfying the hypothesis of [pseudoisomer equilibrium](standard-transformed-gibbs-energy-of-a-reactant.md), with fractions $r_j$, and $\nu'$ is a biochemical reaction with $A'\nu'=0$. (Solvent water, if present, is a one-species group, and on both sides its formation energy carries no concentration term.) Choose one representative species $j(i)\in J_i$ for each reactant and set

$$
n_{\mathrm H}=-\sum_{i\in I'}\nu_i'\,N_{\mathrm H}(j(i)),\qquad n_{\mathrm{Mg}}=-\sum_{i\in I'}\nu_i'\,N_{\mathrm{Mg}}(j(i)).
$$

The reference reaction $\sum_i\nu_i'\mathrm B_{j(i)}+n_{\mathrm H}\mathrm{H^+}+n_{\mathrm{Mg}}\mathrm{Mg^{2+}}=0$ then balances every element. (It is a chemical equation in the usual sense when its charges also balance; nothing below uses charge.) With the [standard Gibbs energies of formation of species](standard-transformed-gibbs-energy-of-a-species.md) at the given $T$ and $I$, define

$$
\Delta_rG^\circ_{\mathrm{ref}}=\sum_i\nu_i'\,\Delta_fG^\circ_{j(i)}+n_{\mathrm H}\Delta_fG^\circ(\mathrm{H^+})+n_{\mathrm{Mg}}\Delta_fG^\circ(\mathrm{Mg^{2+}}),\qquad K_{\mathrm{ref}}=\exp\Bigl(-\frac{\Delta_rG^\circ_{\mathrm{ref}}}{RT}\Bigr),
$$

$$
\Delta_rG_{\mathrm{ref}}=\sum_i\nu_i'\,\Delta_fG_{j(i)}+n_{\mathrm H}\,\mu(\mathrm{H^+})+n_{\mathrm{Mg}}\,\mu(\mathrm{Mg^{2+}}),\qquad \Delta_fG_j=\Delta_fG_j^\circ+RT\ln[\mathrm B_j].
$$

**Statement.** For every choice of representatives:

1. $\Delta_rG_{\mathrm{ref}}=\Delta_rG'$: at pseudoisomer equilibrium the chemical and the biochemical reaction Gibbs energies agree.
2. $\Delta_rG'^\circ=\Delta_rG^\circ_{\mathrm{ref}}-RT\ln(10)\,(n_{\mathrm H}\,\mathrm{pH}+n_{\mathrm{Mg}}\,\mathrm{pMg})+RT\sum_i\nu_i'\ln r_{j(i)}$, so that

$$
K'=K_{\mathrm{ref}}\;10^{\,n_{\mathrm H}\mathrm{pH}+n_{\mathrm{Mg}}\mathrm{pMg}}\prod_{i\in I'}r_{j(i)}^{-\nu_i'}.
$$

3. $K'$ does not depend on the choice of representatives, while $K_{\mathrm{ref}}$, $n_{\mathrm H}$, $n_{\mathrm{Mg}}$ and the factor $\prod_ir_{j(i)}^{-\nu_i'}$ in general do. The number $n_{\mathrm H}$ of hydrogen ions produced by the reference reaction therefore has no mechanistic meaning.

For example, for $\mathrm{ATP}+\mathrm{H_2O}=\mathrm{ADP}+\text{phosphate}$ the representatives $\mathrm{ATP^{4-}}$, $\mathrm{H_2O}$, $\mathrm{ADP^{3-}}$, $\mathrm{HPO_4^{2-}}$ give $n_{\mathrm H}=1$ and the reference reaction $\mathrm{ATP^{4-}}+\mathrm{H_2O}=\mathrm{ADP^{3-}}+\mathrm{HPO_4^{2-}}+\mathrm{H^+}$.

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

Element balance: species of a group share all counts except those of H and Mg, so $A'\nu'=0$ balances the other elements, and $n_{\mathrm H}$, $n_{\mathrm{Mg}}$ are chosen to balance H and Mg. For part 1, substitute $n_{\mathrm H}$ and $n_{\mathrm{Mg}}$: $\Delta_rG_{\mathrm{ref}}=\sum_i\nu_i'(\Delta_fG_{j(i)}-N_{\mathrm H}(j(i))\mu(\mathrm{H^+})-N_{\mathrm{Mg}}(j(i))\mu(\mathrm{Mg^{2+}}))=\sum_i\nu_i'\Delta_fG_{j(i)}'$, and pseudoisomer equilibrium gives $\Delta_fG'_{j(i)}=\Delta_fG_i'$. For part 2, the same substitution in the standard energies gives $\sum_i\nu_i'\Delta_fG'^\circ_{j(i)}=\Delta_rG^\circ_{\mathrm{ref}}-RT\ln(10)(n_{\mathrm H}\mathrm{pH}+n_{\mathrm{Mg}}\mathrm{pMg})$, and $\Delta_fG_i'^\circ=\Delta_fG'^\circ_{j(i)}+RT\ln r_{j(i)}$; exponentiate. Part 3 holds because the left side of part 2 does not mention representatives; with two representatives of one group differing in hydrogen count the values of $n_{\mathrm H}$ differ. The factor $\prod_ir_{j(i)}^{-\nu_i'}$ is the source's function $f(\mathrm{pH})$ of the acid dissociation constants.

## Sources

- R. A. Alberty, A. Cornish-Bowden, R. N. Goldberg, G. G. Hammes, K. Tipton and H. V. Westerhoff, *Recommendations for terminology and databases for biochemical thermodynamics*, IUBMB Recommendations, Biophysical Chemistry 155 (2011) 89–103, <https://doi.org/10.1016/j.bpc.2011.03.007>. Equation numbers are those of the official IUBMB-hosted author manuscript (August 2010, 53 pages), <https://iubmb.qmul.ac.uk/thermod2/BiochemThermodynamics.pdf>: Section 2, equations (2-3)–(2-6) for reference reactions; Section 4, equations (4-5), (4-9) and (4-12); Section 7, equation (7-11) and the remark that $n$ has no mechanistic significance.

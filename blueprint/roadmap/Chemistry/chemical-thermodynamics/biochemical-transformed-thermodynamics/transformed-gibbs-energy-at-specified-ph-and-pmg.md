# Transformed Gibbs energy at specified pH and pMg

The transformed Gibbs energy is the partial Legendre transform of the Gibbs energy that subtracts, for hydrogen and for magnesium, the total amount of the element times the chemical potential of its free ion, which the medium keeps fixed. It makes pH and pMg independent variables of biochemical thermodynamics.

**Data.** Fix a temperature $T>0$, a pressure $P$ and an ionic strength $I$. Let $J$ be a finite set of aqueous species containing the hydrogen ion $\mathrm{H^+}$ and the magnesium ion $\mathrm{Mg^{2+}}$, with amounts $n_j>0$ (in moles) and integer atom counts $N_{\mathrm H}(j)\ge0$ and $N_{\mathrm{Mg}}(j)\ge0$, where

$$
N_{\mathrm H}(\mathrm{H^+})=1,\quad N_{\mathrm{Mg}}(\mathrm{H^+})=0,\quad N_{\mathrm H}(\mathrm{Mg^{2+}})=0,\quad N_{\mathrm{Mg}}(\mathrm{Mg^{2+}})=1 .
$$

Let $\mu_j$ be the molar chemical potentials of the species in an equilibrium state, and $G=U-TS+PV$ its Gibbs energy. Assume the state lies in the domain of a differentiable homogeneous fundamental relation and satisfies $U=TS-PV+\sum_{j\in J}\mu_jn_j$. For the particle-number convention of the linked Euler relation, use $N_j=N_A n_j$ and $\mu_j^{\mathrm{particle}}=\mu_j/N_A$, where $N_A>0$ is the Avogadro constant.

**Component amounts.** The amounts of the hydrogen and magnesium components are the total amounts of these atoms,

$$
n_c(\mathrm H)=\sum_{j\in J}N_{\mathrm H}(j)\,n_j,\qquad n_c(\mathrm{Mg})=\sum_{j\in J}N_{\mathrm{Mg}}(j)\,n_j .
$$

**Fixed free-ion potentials.** Concentrations are divided by $c^\circ=1\ \mathrm{mol\,L^{-1}}$, so $[\mathrm{B}]$ is dimensionless; $\mathrm{pH}=-\log_{10}[\mathrm{H^+}]$ and $\mathrm{pMg}=-\log_{10}[\mathrm{Mg^{2+}}]$ use concentrations, not activities. With the standard Gibbs energies of formation $\Delta_fG^\circ(\mathrm{H^+})$ and $\Delta_fG^\circ(\mathrm{Mg^{2+}})$ at the given $T$ and $I$ (the first is zero at $I=0$ by convention, but not at $I>0$), the medium fixes

$$
\mu(\mathrm{H^+})=\Delta_fG^\circ(\mathrm{H^+})-RT\ln(10)\,\mathrm{pH},\qquad \mu(\mathrm{Mg^{2+}})=\Delta_fG^\circ(\mathrm{Mg^{2+}})-RT\ln(10)\,\mathrm{pMg},
$$

with $R>0$ the gas constant.

**Definition.** The transformed Gibbs energy and the transformed chemical potentials of the species are

$$
G'=G-n_c(\mathrm H)\,\mu(\mathrm{H^+})-n_c(\mathrm{Mg})\,\mu(\mathrm{Mg^{2+}}),
$$

$$
\mu_j'=\mu_j-N_{\mathrm H}(j)\,\mu(\mathrm{H^+})-N_{\mathrm{Mg}}(j)\,\mu(\mathrm{Mg^{2+}})\qquad(j\in J).
$$

For the pH-only variant, omit the magnesium reservoir terms and its specified-potential condition. If no magnesium species is present, omit $\mathrm{Mg^{2+}}$ from $J$ rather than retaining it with zero amount.

**Immediate consequences.**

1. If the free ions in the state are at the specified pH and pMg, that is $\mu_{\mathrm{H^+}}=\mu(\mathrm{H^+})$ and $\mu_{\mathrm{Mg^{2+}}}=\mu(\mathrm{Mg^{2+}})$ for the species potentials, then $\mu'_{\mathrm{H^+}}=\mu'_{\mathrm{Mg^{2+}}}=0$.
2. Since $G=\sum_j\mu_jn_j$ by the Euler relation, $G'=\sum_{j\in J}\mu_j'\,n_j$.

**Sign convention.** Both exchanged terms are subtracted. The source prints its magnesium transform with $+\,n_c(\mathrm{Mg})\mu(\mathrm{Mg^{2+}})$; with that sign consequence 1 fails for $\mathrm{Mg^{2+}}$ ($\mu'_{\mathrm{Mg^{2+}}}$ would be $2\mu(\mathrm{Mg^{2+}})$), and the reciprocal relation printed in the same section would change sign. The minus sign is the one consistent with the source's pH transform and with that relation.

Holding further component potentials fixed, such as that of solvent water or of coenzymes, gives the source's further transformed Gibbs energies $G''$; those transforms are not part of this page.

## Depends on

- [Euler relation for the internal energy](../fundamental-relation-of-thermodynamics/euler-relation.md)
- [Chemical potential from the entropy](../fundamental-relation-of-thermodynamics/chem-pot.md)

## Proof depends on

- [Euler relation for the internal energy](../fundamental-relation-of-thermodynamics/euler-relation.md)

## Expansion

Consequence 1 is $\mu(\mathrm{H^+})-1\cdot\mu(\mathrm{H^+})-0=0$ and the same for $\mathrm{Mg^{2+}}$. For consequence 2, the Euler relation $U=TS-PV+\sum_j\mu_jn_j$ gives $G=\sum_j\mu_jn_j$; substituting the definitions of $n_c(\mathrm H)$ and $n_c(\mathrm{Mg})$ and collecting the coefficient of each $n_j$ gives $\sum_j\mu_j'n_j$. The Euler relation is written with particle numbers and potentials per particle; with amounts in moles and molar potentials it is the same identity after rescaling both by the Avogadro constant.

## Sources

- R. A. Alberty, A. Cornish-Bowden, R. N. Goldberg, G. G. Hammes, K. Tipton and H. V. Westerhoff, *Recommendations for terminology and databases for biochemical thermodynamics*, IUBMB Recommendations, Biophysical Chemistry 155 (2011) 89–103, <https://doi.org/10.1016/j.bpc.2011.03.007>. Section and equation numbers are those of the official IUBMB-hosted author manuscript (August 2010, 53 pages), <https://iubmb.qmul.ac.uk/thermod2/BiochemThermodynamics.pdf>: Section 3, equations (3-1)–(3-4) for Legendre transforms and $G=\sum\mu_jn_j$; Section 5, equations (5-1) and (5-3); Section 7, equation (7-12) for the magnesium transform and equations (7-14) and (7-16) for the further transforms.

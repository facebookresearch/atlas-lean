# Standard transformed Gibbs energy of formation of a species

The standard transformed Gibbs energy of formation of a species shifts its standard Gibbs energy of formation by its numbers of hydrogen and magnesium atoms times the chemical potentials at which the medium keeps the free ions. It depends on temperature, ionic strength, pH and pMg, and is nondecreasing in pH and pMg.

**Setting.** Use the data of the [transformed Gibbs energy](transformed-gibbs-energy-at-specified-ph-and-pmg.md) at fixed $T>0$, $P$, $I$, pH and pMg. Each species $j$ has a standard Gibbs energy of formation $\Delta_fG_j^\circ$ at the given $T$ and $I$, in the biochemical convention in which activity coefficients are absorbed into the standard values, so that $\Delta_fG_j^\circ$ depends on $I$; with a dimensionless concentration $[\mathrm B_j]>0$ its Gibbs energy of formation is

$$
\Delta_fG_j=\Delta_fG_j^\circ+RT\ln[\mathrm B_j],
$$

which plays the role of $\mu_j$.

**Definition.** The standard transformed and the transformed Gibbs energies of formation of species $j$ are

$$
\Delta_fG_j'^\circ=\Delta_fG_j^\circ-N_{\mathrm H}(j)\bigl\{\Delta_fG^\circ(\mathrm{H^+})-RT\ln(10)\,\mathrm{pH}\bigr\}-N_{\mathrm{Mg}}(j)\bigl\{\Delta_fG^\circ(\mathrm{Mg^{2+}})-RT\ln(10)\,\mathrm{pMg}\bigr\},
$$

$$
\Delta_fG_j'=\Delta_fG_j-N_{\mathrm H}(j)\,\mu(\mathrm{H^+})-N_{\mathrm{Mg}}(j)\,\mu(\mathrm{Mg^{2+}}),
$$

the second being the transformed potential $\mu_j'$ written with formation energies.

**Properties.**

1. $\Delta_fG_j'=\Delta_fG_j'^\circ+RT\ln[\mathrm B_j]$.
2. $\partial\Delta_fG_j'^\circ/\partial\,\mathrm{pH}=RT\ln(10)\,N_{\mathrm H}(j)\ge0$ and $\partial\Delta_fG_j'^\circ/\partial\,\mathrm{pMg}=RT\ln(10)\,N_{\mathrm{Mg}}(j)\ge0$; $\Delta_fG_j'^\circ$ is independent of pH and pMg exactly when $N_{\mathrm H}(j)=N_{\mathrm{Mg}}(j)=0$.
3. For the free ions, $\Delta_fG'^\circ(\mathrm{H^+})=RT\ln(10)\,\mathrm{pH}$, and at the specified pH $\Delta_fG'(\mathrm{H^+})=0$; likewise for $\mathrm{Mg^{2+}}$ with pMg.

**Ionic strength (conditional model, pH only).** Assume the extended Debye–Hückel model

$$
\Delta_fG_j^\circ(I)=\Delta_fG_j^\circ(I{=}0)-\alpha z_j^2\frac{\sqrt I}{1+1.6\sqrt I}
$$

for every species including $\mathrm{H^+}$, with $z_j$ the charge number, $\Delta_fG^\circ(\mathrm{H^+})(I{=}0)=0$, $\alpha>0$ the temperature-dependent Debye–Hückel parameter, $I$ in $\mathrm{mol\,kg^{-1}}$ and $1.6\ \mathrm{kg^{1/2}\,mol^{-1/2}}$ an empirical constant taken independent of temperature. For a system without magnesium terms,

$$
\Delta_fG_j'^\circ(I)=\Delta_fG_j^\circ(I{=}0)+N_{\mathrm H}(j)\,RT\ln(10)\,\mathrm{pH}-\alpha\bigl(z_j^2-N_{\mathrm H}(j)\bigr)\frac{\sqrt I}{1+1.6\sqrt I}.
$$

So $\Delta_fG_j'^\circ$ depends on $I$ unless $z_j^2=N_{\mathrm H}(j)$, in particular for uncharged species containing hydrogen. The source prints this formula with $-N_{\mathrm H}(j)RT\ln(10)\,\mathrm{pH}$; substituting the model into the definition gives the plus sign, which is also the sign required by property 2.

## Depends on

- [Transformed Gibbs energy at specified pH and pMg](transformed-gibbs-energy-at-specified-ph-and-pmg.md)

## Proof depends on

- [Transformed Gibbs energy at specified pH and pMg](transformed-gibbs-energy-at-specified-ph-and-pmg.md)

## Expansion

Property 1: substitute $\Delta_fG_j=\Delta_fG_j^\circ+RT\ln[\mathrm B_j]$, $\mu(\mathrm{H^+})=\Delta_fG^\circ(\mathrm{H^+})-RT\ln(10)\,\mathrm{pH}$ and the magnesium analogue into the definition of $\Delta_fG_j'$. Property 2 is differentiation of an affine function of pH and pMg. Property 3 uses $N_{\mathrm H}(\mathrm{H^+})=1$ and $\ln[\mathrm{H^+}]=-\ln(10)\,\mathrm{pH}$. For the ionic-strength formula, $-N_{\mathrm H}(j)\{\Delta_fG^\circ(\mathrm{H^+})(I)-RT\ln(10)\,\mathrm{pH}\}$ with $\Delta_fG^\circ(\mathrm{H^+})(I)=-\alpha\sqrt I/(1+1.6\sqrt I)$ equals $+N_{\mathrm H}(j)RT\ln(10)\,\mathrm{pH}+N_{\mathrm H}(j)\alpha\sqrt I/(1+1.6\sqrt I)$, which combines with the species term. The magnesium version follows by the same substitution with charge number $2$ for $\mathrm{Mg^{2+}}$; it is not printed in the source and is not stated here.

## Sources

- R. A. Alberty, A. Cornish-Bowden, R. N. Goldberg, G. G. Hammes, K. Tipton and H. V. Westerhoff, *Recommendations for terminology and databases for biochemical thermodynamics*, IUBMB Recommendations, Biophysical Chemistry 155 (2011) 89–103, <https://doi.org/10.1016/j.bpc.2011.03.007>. Equation numbers are those of the official IUBMB-hosted author manuscript (August 2010, 53 pages), <https://iubmb.qmul.ac.uk/thermod2/BiochemThermodynamics.pdf>: Section 4, equations (4-7)–(4-9) for the ionic-strength convention; Section 6, equations (6-1)–(6-5); Section 7, equation (7-12) for the magnesium terms.

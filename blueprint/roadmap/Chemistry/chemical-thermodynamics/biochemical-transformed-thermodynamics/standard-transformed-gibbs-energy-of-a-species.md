# Standard transformed Gibbs energy of formation of a species

The standard transformed Gibbs energy of formation of a species shifts its standard Gibbs energy of formation by its numbers of hydrogen and magnesium atoms times the chemical potentials at which the medium keeps the free ions. It depends on temperature, ionic strength, pH and pMg, and is nondecreasing in pH and pMg.

**Setting.** Use the data of the [transformed Gibbs energy](transformed-gibbs-energy-at-specified-ph-and-pmg.md) at fixed $T>0$, $P$, $I$, pH and pMg. Each species $j$ has a standard Gibbs energy of formation $\Delta_fG_j^\circ$ at the given $T$ and $I$, in the biochemical convention in which activity coefficients are absorbed into the standard values, so that $\Delta_fG_j^\circ$ depends on $I$; with a dimensionless concentration $[\mathrm B_j]>0$ its Gibbs energy of formation is

$$
\Delta_fG_j=\Delta_fG_j^\circ+RT\ln[\mathrm B_j],
$$

which plays the role of $\mu_j$.

**Definition.** The standard transformed and the transformed Gibbs energies of formation of species $j$ at specified pH and pMg are

$$
\Delta_fG_j'^\circ=\Delta_fG_j^\circ-N_{\mathrm H}(j)\bigl\{\Delta_fG^\circ(\mathrm{H^+})-RT\ln(10)\,\mathrm{pH}\bigr\}-N_{\mathrm{Mg}}(j)\bigl\{\Delta_fG^\circ(\mathrm{Mg^{2+}})-RT\ln(10)\,\mathrm{pMg}\bigr\},
$$

$$
\Delta_fG_j'=\Delta_fG_j-N_{\mathrm H}(j)\,\mu(\mathrm{H^+})-N_{\mathrm{Mg}}(j)\,\mu(\mathrm{Mg^{2+}}),
$$

the second being the transformed potential $\mu_j'$ written with formation energies. For the pH-only variant, at specified pH with pMg not specified, omit the magnesium terms. The 2011 manuscript prints the species formulas only for that variant. The magnesium terms are the direct specialization of the two-reservoir transform, whose minus sign corrects that manuscript's printed magnesium transform, and the 1994 recommendations print the two-reservoir species formula; for a species with $N_{\mathrm{Mg}}(j)=0$ the two forms agree.

**Properties.**

1. $\Delta_fG_j'=\Delta_fG_j'^\circ+RT\ln[\mathrm B_j]$.
2. $\partial\Delta_fG_j'^\circ/\partial\,\mathrm{pH}=RT\ln(10)\,N_{\mathrm H}(j)\ge0$ and $\partial\Delta_fG_j'^\circ/\partial\,\mathrm{pMg}=RT\ln(10)\,N_{\mathrm{Mg}}(j)\ge0$; $\Delta_fG_j'^\circ$ is independent of pH and pMg exactly when $N_{\mathrm H}(j)=N_{\mathrm{Mg}}(j)=0$.
3. For the free ions, $\Delta_fG'^\circ(\mathrm{H^+})=RT\ln(10)\,\mathrm{pH}$ and $\Delta_fG'^\circ(\mathrm{Mg^{2+}})=RT\ln(10)\,\mathrm{pMg}$, and at the specified pH and pMg $\Delta_fG'(\mathrm{H^+})=\Delta_fG'(\mathrm{Mg^{2+}})=0$.

**Ionic strength (conditional model, pH-only variant).** Assume the extended Debye–Hückel model

$$
\Delta_fG_j^\circ(I)=\Delta_fG_j^\circ(I{=}0)-\alpha z_j^2\frac{\sqrt I}{1+1.6\sqrt I}
$$

for every species including $\mathrm{H^+}$, with $z_j$ the charge number, $\Delta_fG^\circ(\mathrm{H^+})(I{=}0)=0$, $\alpha>0$ the temperature-dependent Debye–Hückel parameter, $I$ in $\mathrm{mol\,kg^{-1}}$ and $1.6\ \mathrm{kg^{1/2}\,mol^{-1/2}}$ an empirical constant taken independent of temperature. Under this model, in the pH-only variant,

$$
\Delta_fG_j'^\circ(I)=\Delta_fG_j^\circ(I{=}0)+N_{\mathrm H}(j)\,RT\ln(10)\,\mathrm{pH}-\alpha\bigl(z_j^2-N_{\mathrm H}(j)\bigr)\frac{\sqrt I}{1+1.6\sqrt I}.
$$

So $\Delta_fG_j'^\circ$ depends on $I$ unless $z_j^2=N_{\mathrm H}(j)$, in particular for uncharged species containing hydrogen. The 2011 manuscript prints this formula with $-N_{\mathrm H}(j)RT\ln(10)\,\mathrm{pH}$; substituting the model into the definition gives the plus sign, which is also the sign required by property 2.

## Depends on

- [Transformed Gibbs energy at specified pH and pMg](transformed-gibbs-energy-at-specified-ph-and-pmg.md)

## Proof depends on

- [Transformed Gibbs energy at specified pH and pMg](transformed-gibbs-energy-at-specified-ph-and-pmg.md)

## Expansion

Property 1: substitute $\Delta_fG_j=\Delta_fG_j^\circ+RT\ln[\mathrm B_j]$, $\mu(\mathrm{H^+})=\Delta_fG^\circ(\mathrm{H^+})-RT\ln(10)\,\mathrm{pH}$ and $\mu(\mathrm{Mg^{2+}})=\Delta_fG^\circ(\mathrm{Mg^{2+}})-RT\ln(10)\,\mathrm{pMg}$ into the definition of $\Delta_fG_j'$. Property 2 is differentiation of an affine function of pH and pMg. Property 3 uses $N_{\mathrm H}(\mathrm{H^+})=N_{\mathrm{Mg}}(\mathrm{Mg^{2+}})=1$, $N_{\mathrm{Mg}}(\mathrm{H^+})=N_{\mathrm H}(\mathrm{Mg^{2+}})=0$, $\ln[\mathrm{H^+}]=-\ln(10)\,\mathrm{pH}$ and $\ln[\mathrm{Mg^{2+}}]=-\ln(10)\,\mathrm{pMg}$. For the ionic-strength formula, $-N_{\mathrm H}(j)\{\Delta_fG^\circ(\mathrm{H^+})(I)-RT\ln(10)\,\mathrm{pH}\}$ with $\Delta_fG^\circ(\mathrm{H^+})(I)=-\alpha\sqrt I/(1+1.6\sqrt I)$ equals $+N_{\mathrm H}(j)RT\ln(10)\,\mathrm{pH}+N_{\mathrm H}(j)\alpha\sqrt I/(1+1.6\sqrt I)$, which combines with the species term. A Debye–Hückel version with magnesium terms follows by the same substitution with charge number $2$ for $\mathrm{Mg^{2+}}$; it is not printed in the 2011 manuscript and is not stated here.

## Sources

- R. A. Alberty, A. Cornish-Bowden, R. N. Goldberg, G. G. Hammes, K. Tipton and H. V. Westerhoff, *Recommendations for terminology and databases for biochemical thermodynamics*, IUBMB Recommendations, Biophysical Chemistry 155 (2011) 89–103, <https://doi.org/10.1016/j.bpc.2011.03.007>. Equation numbers are those of the official IUBMB-hosted author manuscript (August 2010, 53 pages), <https://iubmb.qmul.ac.uk/thermod2/BiochemThermodynamics.pdf>: Section 4, equations (4-7)–(4-9) for the ionic-strength convention; Section 6, equations (6-1)–(6-5) for the pH-only species formulas; Section 7, equation (7-12), with its sign corrected, for the magnesium terms.
- R. A. Alberty, A. Cornish-Bowden, Q. H. Gibson, R. N. Goldberg, G. G. Hammes, W. Jencks, K. F. Tipton, R. Veech, H. V. Westerhoff and E. C. Webb (IUPAC–IUBMB Panel on Biochemical Thermodynamics), *Recommendations for nomenclature and tables in biochemical thermodynamics* (Recommendations 1994), Pure Appl. Chem. 66 (1994) 1641–1666, reprinted in Eur. J. Biochem. 240 (1996) 1–14. Equation numbers are those of the IUBMB web version, Section 5, <https://iubmb.qmul.ac.uk/thermod/noGreek/th5.html>: equation (60), the standard transformed Gibbs energy of formation of a species with hydrogen and magnesium terms.

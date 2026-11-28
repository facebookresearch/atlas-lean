# Standard transformed Gibbs energy of formation of a species

The standard transformed Gibbs energy of formation of a species shifts its standard Gibbs energy of formation by its number of hydrogen atoms times the chemical potential at which the medium keeps the free hydrogen ion. It depends on temperature, ionic strength and pH, and is nondecreasing in pH.

**Setting.** Use the data of the [transformed Gibbs energy](transformed-gibbs-energy-at-specified-ph-and-pmg.md) at fixed $T>0$, $P$, $I$ and pH. Each species $j$ has a standard Gibbs energy of formation $\Delta_fG_j^\circ$ at the given $T$ and $I$, in the biochemical convention in which activity coefficients are absorbed into the standard values, so that $\Delta_fG_j^\circ$ depends on $I$; with a dimensionless concentration $[\mathrm B_j]>0$ its Gibbs energy of formation is

$$
\Delta_fG_j=\Delta_fG_j^\circ+RT\ln[\mathrm B_j],
$$

which plays the role of $\mu_j$.

**Definition.** The standard transformed and the transformed Gibbs energies of formation of species $j$ at specified pH are

$$
\Delta_fG_j'^\circ=\Delta_fG_j^\circ-N_{\mathrm H}(j)\bigl\{\Delta_fG^\circ(\mathrm{H^+})-RT\ln(10)\,\mathrm{pH}\bigr\},
$$

$$
\Delta_fG_j'=\Delta_fG_j-N_{\mathrm H}(j)\,\mu(\mathrm{H^+}),
$$

the second being the transformed potential $\mu_j'$ of the pH-only transform written with formation energies.

**Properties.**

1. $\Delta_fG_j'=\Delta_fG_j'^\circ+RT\ln[\mathrm B_j]$.
2. $\partial\Delta_fG_j'^\circ/\partial\,\mathrm{pH}=RT\ln(10)\,N_{\mathrm H}(j)\ge0$; $\Delta_fG_j'^\circ$ is independent of pH exactly when $N_{\mathrm H}(j)=0$.
3. For the free ion, $\Delta_fG'^\circ(\mathrm{H^+})=RT\ln(10)\,\mathrm{pH}$, and at the specified pH $\Delta_fG'(\mathrm{H^+})=0$.

**Ionic strength (conditional model).** Assume the extended Debye–Hückel model

$$
\Delta_fG_j^\circ(I)=\Delta_fG_j^\circ(I{=}0)-\alpha z_j^2\frac{\sqrt I}{1+1.6\sqrt I}
$$

for every species including $\mathrm{H^+}$, with $z_j$ the charge number, $\Delta_fG^\circ(\mathrm{H^+})(I{=}0)=0$, $\alpha>0$ the temperature-dependent Debye–Hückel parameter, $I$ in $\mathrm{mol\,kg^{-1}}$ and $1.6\ \mathrm{kg^{1/2}\,mol^{-1/2}}$ an empirical constant taken independent of temperature. Under this model,

$$
\Delta_fG_j'^\circ(I)=\Delta_fG_j^\circ(I{=}0)+N_{\mathrm H}(j)\,RT\ln(10)\,\mathrm{pH}-\alpha\bigl(z_j^2-N_{\mathrm H}(j)\bigr)\frac{\sqrt I}{1+1.6\sqrt I}.
$$

So $\Delta_fG_j'^\circ$ depends on $I$ unless $z_j^2=N_{\mathrm H}(j)$, in particular for uncharged species containing hydrogen. The source prints this formula with $-N_{\mathrm H}(j)RT\ln(10)\,\mathrm{pH}$; substituting the model into the definition gives the plus sign, which is also the sign required by property 2.

## Derived extensions

**Magnesium terms.** The source prints no species-level magnesium formula. With the two-reservoir transform of the [transformed Gibbs energy](transformed-gibbs-energy-at-specified-ph-and-pmg.md), whose minus sign corrects the source's printed magnesium transform, the same construction gives

$$
\Delta_fG_j'^\circ=\Delta_fG_j^\circ-N_{\mathrm H}(j)\bigl\{\Delta_fG^\circ(\mathrm{H^+})-RT\ln(10)\,\mathrm{pH}\bigr\}-N_{\mathrm{Mg}}(j)\bigl\{\Delta_fG^\circ(\mathrm{Mg^{2+}})-RT\ln(10)\,\mathrm{pMg}\bigr\},
$$

$$
\Delta_fG_j'=\Delta_fG_j-N_{\mathrm H}(j)\,\mu(\mathrm{H^+})-N_{\mathrm{Mg}}(j)\,\mu(\mathrm{Mg^{2+}}).
$$

Properties 1–3 then hold with the pMg analogues: $\Delta_fG_j'=\Delta_fG_j'^\circ+RT\ln[\mathrm B_j]$; $\partial\Delta_fG_j'^\circ/\partial\,\mathrm{pMg}=RT\ln(10)\,N_{\mathrm{Mg}}(j)\ge0$; $\Delta_fG_j'^\circ$ is independent of pH and pMg exactly when $N_{\mathrm H}(j)=N_{\mathrm{Mg}}(j)=0$; and $\Delta_fG'(\mathrm{Mg^{2+}})=0$ at the specified pMg. *Proof.* Substitute $\mu(\mathrm{Mg^{2+}})=\Delta_fG^\circ(\mathrm{Mg^{2+}})-RT\ln(10)\,\mathrm{pMg}$ exactly as $\mu(\mathrm{H^+})$ is substituted below; the expression is affine in pH and pMg. The Debye–Hückel version with magnesium follows by the same substitution with charge number $2$ for $\mathrm{Mg^{2+}}$ and is not stated here.

## Depends on

- [Transformed Gibbs energy at specified pH and pMg](transformed-gibbs-energy-at-specified-ph-and-pmg.md)

## Proof depends on

- [Transformed Gibbs energy at specified pH and pMg](transformed-gibbs-energy-at-specified-ph-and-pmg.md)

## Expansion

Property 1: substitute $\Delta_fG_j=\Delta_fG_j^\circ+RT\ln[\mathrm B_j]$ and $\mu(\mathrm{H^+})=\Delta_fG^\circ(\mathrm{H^+})-RT\ln(10)\,\mathrm{pH}$ into the definition of $\Delta_fG_j'$. Property 2 is differentiation of an affine function of pH. Property 3 uses $N_{\mathrm H}(\mathrm{H^+})=1$ and $\ln[\mathrm{H^+}]=-\ln(10)\,\mathrm{pH}$. For the ionic-strength formula, $-N_{\mathrm H}(j)\{\Delta_fG^\circ(\mathrm{H^+})(I)-RT\ln(10)\,\mathrm{pH}\}$ with $\Delta_fG^\circ(\mathrm{H^+})(I)=-\alpha\sqrt I/(1+1.6\sqrt I)$ equals $+N_{\mathrm H}(j)RT\ln(10)\,\mathrm{pH}+N_{\mathrm H}(j)\alpha\sqrt I/(1+1.6\sqrt I)$, which combines with the species term.

## Sources

- R. A. Alberty, A. Cornish-Bowden, R. N. Goldberg, G. G. Hammes, K. Tipton and H. V. Westerhoff, *Recommendations for terminology and databases for biochemical thermodynamics*, IUBMB Recommendations, Biophysical Chemistry 155 (2011) 89–103, <https://doi.org/10.1016/j.bpc.2011.03.007>. Equation numbers are those of the official IUBMB-hosted author manuscript (August 2010, 53 pages), <https://iubmb.qmul.ac.uk/thermod2/BiochemThermodynamics.pdf>: Section 4, equations (4-7)–(4-9) for the ionic-strength convention; Section 6, equations (6-1)–(6-5) for the main statement; Section 7, equation (7-12) for the magnesium transform of the derived extension.

# Change in binding of hydrogen ions in a biochemical reaction

The pH-slope of the standard transformed Gibbs energy of a biochemical reaction is $RT\ln10$ times the change in the average number of bound hydrogen atoms. So the apparent equilibrium constant rises with pH exactly when the reaction releases hydrogen ions to the medium, and the same holds for magnesium and pMg.

**Setting.** Let $\nu'$ be a biochemical reaction on reactants $i\in I'$, with $\Delta_rG'^\circ$, $K'$ and $\Delta_rG'$ as for the [apparent equilibrium constant](apparent-equilibrium-constant.md), and suppose every reactant satisfies the smoothness hypotheses of [the derivatives of the standard transformed Gibbs energy of a reactant](derivatives-of-standard-transformed-gibbs-energy.md), with mean counts $\bar N_{\mathrm H}(i)$ and $\bar N_{\mathrm{Mg}}(i)$ (solvent water has the constant counts $\bar N_{\mathrm H}=2$, $\bar N_{\mathrm{Mg}}=0$). The changes in binding of hydrogen and magnesium in the reaction are

$$
\Delta_rN_{\mathrm H}=\sum_{i\in I'}\nu_i'\,\bar N_{\mathrm H}(i),\qquad \Delta_rN_{\mathrm{Mg}}=\sum_{i\in I'}\nu_i'\,\bar N_{\mathrm{Mg}}(i).
$$

**Statement.** At fixed $T>0$, $P$ and $I$:

1.

$$
\frac{\partial\Delta_rG'^\circ}{\partial\,\mathrm{pH}}=RT\ln(10)\,\Delta_rN_{\mathrm H},\qquad \frac{\partial\Delta_rG'^\circ}{\partial\,\mathrm{pMg}}=RT\ln(10)\,\Delta_rN_{\mathrm{Mg}};
$$

2. $\partial\log_{10}K'/\partial\,\mathrm{pH}=-\Delta_rN_{\mathrm H}$ and $\partial\log_{10}K'/\partial\,\mathrm{pMg}=-\Delta_rN_{\mathrm{Mg}}$; in particular $K'$ increases with pH where $\Delta_rN_{\mathrm H}<0$, that is where the products bind fewer hydrogen atoms on average than the reactants and the reaction releases hydrogen ions to the buffer;
3. at fixed reactant concentrations, $\partial\Delta_rG'/\partial\,\mathrm{pH}=\partial\Delta_rG'^\circ/\partial\,\mathrm{pH}$ and likewise for pMg;
4. $\partial\Delta_rN_{\mathrm H}/\partial\,\mathrm{pMg}=\partial\Delta_rN_{\mathrm{Mg}}/\partial\,\mathrm{pH}$.

## Depends on

- [Apparent equilibrium constant and transformed reaction Gibbs energy](apparent-equilibrium-constant.md)
- [Temperature, pH and pMg derivatives of the standard transformed Gibbs energy of a reactant](derivatives-of-standard-transformed-gibbs-energy.md)

## Proof depends on

- [Apparent equilibrium constant and transformed reaction Gibbs energy](apparent-equilibrium-constant.md)
- [Temperature, pH and pMg derivatives of the standard transformed Gibbs energy of a reactant](derivatives-of-standard-transformed-gibbs-energy.md)

## Expansion

$\Delta_rG'^\circ=\sum_i\nu_i'\Delta_fG_i'^\circ$ is a fixed linear combination, so part 1 follows from the reactant-level binding derivatives term by term, and part 4 from the reactant-level reciprocal effect. Part 2 divides part 1 by $-RT\ln(10)$, since $\log_{10}K'=-\Delta_rG'^\circ/(RT\ln 10)$. Part 3 holds because $\Delta_rG'-\Delta_rG'^\circ=RT\ln Q'$ involves only the reactant concentrations. The sign in part 2 matches the factor $10^{n_{\mathrm H}\mathrm{pH}}$ of a reference reaction that produces $n_{\mathrm H}$ hydrogen ions.

## Sources

- R. A. Alberty, A. Cornish-Bowden, R. N. Goldberg, G. G. Hammes, K. Tipton and H. V. Westerhoff, *Recommendations for terminology and databases for biochemical thermodynamics*, IUBMB Recommendations, Biophysical Chemistry 155 (2011) 89–103, <https://doi.org/10.1016/j.bpc.2011.03.007>. Equation numbers are those of the official IUBMB-hosted author manuscript (August 2010, 53 pages), <https://iubmb.qmul.ac.uk/thermod2/BiochemThermodynamics.pdf>: Section 7, equations (7-4)–(7-6), (7-9), (7-11) and (7-13).

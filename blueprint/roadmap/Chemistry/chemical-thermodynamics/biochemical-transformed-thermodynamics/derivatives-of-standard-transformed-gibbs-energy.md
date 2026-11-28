# Temperature, pH and pMg derivatives of the standard transformed Gibbs energy of a reactant

Differentiating the standard transformed Gibbs energy of a reactant gives its average numbers of bound hydrogen and magnesium atoms and its transformed enthalpy and entropy. The mixed derivatives give the reciprocal effect: the pMg-dependence of hydrogen binding equals the pH-dependence of magnesium binding.

**Setting.** Let $J_i$ be a pseudoisomer group at fixed $P$ and $I$, as in [the standard transformed Gibbs energy of a pseudoisomer group](standard-transformed-gibbs-energy-of-a-reactant.md), with fractions $r_j$. Assume that the standard Gibbs energies of formation $\Delta_fG_j^\circ(T)$ of its species and $\Delta_fG^\circ(\mathrm{H^+})(T)$, $\Delta_fG^\circ(\mathrm{Mg^{2+}})(T)$ are twice continuously differentiable on an open interval of temperatures $T>0$. Write $g_i(T,\mathrm{pH},\mathrm{pMg})=\Delta_fG_i'^\circ$ on that interval times $\mathbb R^2$, and set

$$
\bar N_{\mathrm H}(i)=\sum_{j\in J_i}r_jN_{\mathrm H}(j),\qquad \bar N_{\mathrm{Mg}}(i)=\sum_{j\in J_i}r_jN_{\mathrm{Mg}}(j),
$$

$$
\Delta_fS_i'^\circ=-\frac{\partial g_i}{\partial T},\qquad \Delta_fH_i'^\circ=-T^2\frac{\partial(g_i/T)}{\partial T},\qquad \Delta_fH_j'^\circ=-T^2\frac{\partial(\Delta_fG_j'^\circ/T)}{\partial T},
$$

with $T$-derivatives at fixed pH, pMg and $I$, and $\Delta_fH^\circ=-T^2\,\partial(\Delta_fG^\circ/T)/\partial T$ for each untransformed standard energy.

**Statement.** The function $g_i$ is twice continuously differentiable, and:

1. (hydrogen and magnesium binding)

$$
\frac{\partial g_i}{\partial\,\mathrm{pH}}=RT\ln(10)\,\bar N_{\mathrm H}(i),\qquad \frac{\partial g_i}{\partial\,\mathrm{pMg}}=RT\ln(10)\,\bar N_{\mathrm{Mg}}(i);
$$

2. (reciprocal effect) the first derivative at fixed pH, the second at fixed pMg,

$$
\frac{\partial\bar N_{\mathrm H}(i)}{\partial\,\mathrm{pMg}}=\frac{\partial\bar N_{\mathrm{Mg}}(i)}{\partial\,\mathrm{pH}}=-\ln(10)\sum_{j\in J_i}r_j\bigl(N_{\mathrm H}(j)-\bar N_{\mathrm H}(i)\bigr)\bigl(N_{\mathrm{Mg}}(j)-\bar N_{\mathrm{Mg}}(i)\bigr);
$$

3. (transformed enthalpy) $\Delta_fH_j'^\circ=\Delta_fH_j^\circ-N_{\mathrm H}(j)\Delta_fH^\circ(\mathrm{H^+})-N_{\mathrm{Mg}}(j)\Delta_fH^\circ(\mathrm{Mg^{2+}})$, independent of pH and pMg, and

$$
\Delta_fH_i'^\circ=\sum_{j\in J_i}r_j\,\Delta_fH_j'^\circ;
$$

4. (pH dependence of enthalpy and entropy)

$$
\frac{\partial\Delta_fH_i'^\circ}{\partial\,\mathrm{pH}}=-RT^2\ln(10)\frac{\partial\bar N_{\mathrm H}(i)}{\partial T},\qquad -\frac{\partial\Delta_fS_i'^\circ}{\partial\,\mathrm{pH}}=R\ln(10)\frac{\partial\bigl(T\bar N_{\mathrm H}(i)\bigr)}{\partial T}.
$$

The source prints the entropy relation with $\partial/\partial T$ on the left and $RT\ln(10)$ on the right, which is dimensionally inconsistent; the form above is what the mixed partial derivatives of $g_i$ give. The diagonal derivative $\partial\bar N_{\mathrm H}/\partial\,\mathrm{pH}$ is the occupancy-variance identity of binding polynomials and is not restated here.

## Depends on

- [Standard transformed Gibbs energy of a pseudoisomer group](standard-transformed-gibbs-energy-of-a-reactant.md)
- [Standard transformed Gibbs energy of formation of a species](standard-transformed-gibbs-energy-of-a-species.md)

## Proof depends on

- [Standard transformed Gibbs energy of a pseudoisomer group](standard-transformed-gibbs-energy-of-a-reactant.md)
- [Standard transformed Gibbs energy of formation of a species](standard-transformed-gibbs-energy-of-a-species.md)
- [Helmholtz free energy from the partition function](../canonical-ensemble-of-a-finite-system/helmholtz-free-energy.md)
- [Logarithm of a Boltzmann probability](../canonical-ensemble-of-a-finite-system/log-boltzmann-prob.md)

## Expansion

Differentiating the finite positive partition sum at fixed $T$ gives $\partial g_i/\partial x=\sum_jr_j\,\partial\Delta_fG_j'^\circ/\partial x$ for $x\in\{\mathrm{pH},\mathrm{pMg}\}$; with $\partial\Delta_fG_j'^\circ/\partial\,\mathrm{pH}=RT\ln(10)N_{\mathrm H}(j)$ this gives part 1. Since $\ln r_j=(g_i-\Delta_fG_j'^\circ)/RT$, $\partial\ln r_j/\partial\,\mathrm{pMg}=-\ln(10)(N_{\mathrm{Mg}}(j)-\bar N_{\mathrm{Mg}}(i))$, and differentiating $\bar N_{\mathrm H}(i)$ gives the covariance in part 2, which is symmetric in the two counts. For part 3, $g_i/T=-R\ln\sum_j\exp(-\Delta_fG_j'^\circ/(RT))$, whose $T$-derivative is $\sum_jr_j\,\partial(\Delta_fG_j'^\circ/T)/\partial T$; the term $N_{\mathrm H}(j)R\ln(10)\,\mathrm{pH}$ of $\Delta_fG_j'^\circ/T$ does not depend on $T$. Part 4 exchanges the order of the mixed partial derivatives of $g_i/T$ and of $g_i$ in $T$ and pH, using part 1.

## Sources

- R. A. Alberty, A. Cornish-Bowden, R. N. Goldberg, G. G. Hammes, K. Tipton and H. V. Westerhoff, *Recommendations for terminology and databases for biochemical thermodynamics*, IUBMB Recommendations, Biophysical Chemistry 155 (2011) 89–103, <https://doi.org/10.1016/j.bpc.2011.03.007>. Equation numbers are those of the official IUBMB-hosted author manuscript (August 2010, 53 pages), <https://iubmb.qmul.ac.uk/thermod2/BiochemThermodynamics.pdf>: Section 5, equations (5-6)–(5-10); Section 6, equations (6-7)–(6-10); Section 7, equation (7-13).

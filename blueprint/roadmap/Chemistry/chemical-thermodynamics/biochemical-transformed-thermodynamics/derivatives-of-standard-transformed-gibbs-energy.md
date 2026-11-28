# Temperature, pH and pMg derivatives of the standard transformed Gibbs energy of a reactant

Differentiating the standard transformed Gibbs energy of a reactant in pH gives its average number of bound hydrogen atoms, and differentiating in temperature gives its transformed entropy and enthalpy. The mixed derivatives in pH and pMg give the reciprocal effect: the pMg-dependence of hydrogen binding equals the pH-dependence of magnesium binding.

**Setting.** Let $J_i$ be a pseudoisomer group at fixed $P$, $I$ and pMg, as in [the standard transformed Gibbs energy of a pseudoisomer group](standard-transformed-gibbs-energy-of-a-reactant.md), with fractions $r_j$. Its species energies are those of the [species page](standard-transformed-gibbs-energy-of-a-species.md). Assume that the standard Gibbs energies of formation $\Delta_fG_j^\circ(T)$ of its species, $\Delta_fG^\circ(\mathrm{H^+})(T)$ and $\Delta_fG^\circ(\mathrm{Mg^{2+}})(T)$ are twice continuously differentiable on an open interval of temperatures $T>0$. Write $g_i(T,\mathrm{pH})=\Delta_fG_i'^\circ$ at the fixed pMg, on that interval times $\mathbb R$, and set

$$
\bar N_{\mathrm H}(i)=\sum_{j\in J_i}r_jN_{\mathrm H}(j),
$$

$$
\Delta_fS_i'^\circ=-\frac{\partial g_i}{\partial T},\qquad \Delta_fH_i'^\circ=-T^2\frac{\partial(g_i/T)}{\partial T},\qquad \Delta_fH_j'^\circ=-T^2\frac{\partial(\Delta_fG_j'^\circ/T)}{\partial T},
$$

with $T$-derivatives at fixed pH, pMg and $I$.

**Statement.** The function $g_i$ is twice continuously differentiable, and:

1. (hydrogen binding)

    $$
    \frac{\partial g_i}{\partial\,\mathrm{pH}}=RT\ln(10)\,\bar N_{\mathrm H}(i);
    $$

2. (transformed enthalpy)

    $$
    \Delta_fH_i'^\circ=\sum_{j\in J_i}r_j\,\Delta_fH_j'^\circ;
    $$

3. (pH dependence of enthalpy and entropy)

    $$
    \frac{\partial\Delta_fH_i'^\circ}{\partial\,\mathrm{pH}}=-RT^2\ln(10)\frac{\partial\bar N_{\mathrm H}(i)}{\partial T},\qquad -\frac{\partial\Delta_fS_i'^\circ}{\partial\,\mathrm{pH}}=R\ln(10)\frac{\partial\bigl(T\bar N_{\mathrm H}(i)\bigr)}{\partial T};
    $$

4. (reciprocal effect) with $g_i=g_i(T,\mathrm{pH},\mathrm{pMg})$ regarded as a function on the interval times $\mathbb R^2$ and $\bar N_{\mathrm{Mg}}(i)=\sum_{j\in J_i}r_jN_{\mathrm{Mg}}(j)$, then, the first derivative at fixed pH and the second at fixed pMg,

    $$
    \frac{\partial\bar N_{\mathrm H}(i)}{\partial\,\mathrm{pMg}}=\frac{\partial\bar N_{\mathrm{Mg}}(i)}{\partial\,\mathrm{pH}}.
    $$

The source prints the entropy relation in part 3 with $\partial/\partial T$ on the left and $RT\ln(10)$ on the right, which is dimensionally inconsistent; the form above is what the mixed partial derivatives of $g_i$ give. The diagonal derivative $\partial\bar N_{\mathrm H}/\partial\,\mathrm{pH}$ is the occupancy-variance identity of binding polynomials and is not restated here.

## Derived extensions

These statements are not printed in the source, and each is proved here. Only the magnesium-binding extension is used in the main proof, for part 4.

**Magnesium binding.** In the setting of part 4, $\partial g_i/\partial\,\mathrm{pMg}=RT\ln(10)\,\bar N_{\mathrm{Mg}}(i)$. *Proof.* As for part 1, with $\partial\Delta_fG_j'^\circ/\partial\,\mathrm{pMg}=RT\ln(10)N_{\mathrm{Mg}}(j)$.

**Covariance form of the reciprocal effect.** In the setting of part 4, both sides of part 4 equal

$$
-\ln(10)\sum_{j\in J_i}r_j\bigl(N_{\mathrm H}(j)-\bar N_{\mathrm H}(i)\bigr)\bigl(N_{\mathrm{Mg}}(j)-\bar N_{\mathrm{Mg}}(i)\bigr).
$$

*Proof.* Since $\ln r_j=(g_i-\Delta_fG_j'^\circ)/RT$, the pMg-extension of part 1 gives $\partial\ln r_j/\partial\,\mathrm{pMg}=-\ln(10)(N_{\mathrm{Mg}}(j)-\bar N_{\mathrm{Mg}}(i))$, and differentiating $\bar N_{\mathrm H}(i)=\sum_jr_jN_{\mathrm H}(j)$ gives the covariance; exchanging the two counts gives the other side.

**Species transformed enthalpy.** With $\Delta_fH^\circ=-T^2\,\partial(\Delta_fG^\circ/T)/\partial T$ for each untransformed standard energy, $\Delta_fH_j'^\circ=\Delta_fH_j^\circ-N_{\mathrm H}(j)\Delta_fH^\circ(\mathrm{H^+})-N_{\mathrm{Mg}}(j)\Delta_fH^\circ(\mathrm{Mg^{2+}})$, independent of pH and pMg. *Proof.* The terms $N_{\mathrm H}(j)R\ln(10)\,\mathrm{pH}$ and $N_{\mathrm{Mg}}(j)R\ln(10)\,\mathrm{pMg}$ of $\Delta_fG_j'^\circ/T$ do not depend on $T$, and the other terms are linear in the untransformed standard energies.

## Depends on

- [Standard transformed Gibbs energy of a pseudoisomer group](standard-transformed-gibbs-energy-of-a-reactant.md)
- [Standard transformed Gibbs energy of formation of a species](standard-transformed-gibbs-energy-of-a-species.md)

## Proof depends on

- [Standard transformed Gibbs energy of a pseudoisomer group](standard-transformed-gibbs-energy-of-a-reactant.md)
- [Standard transformed Gibbs energy of formation of a species](standard-transformed-gibbs-energy-of-a-species.md)
- [Helmholtz free energy from the partition function](../canonical-ensemble-of-a-finite-system/helmholtz-free-energy.md)
- [Logarithm of a Boltzmann probability](../canonical-ensemble-of-a-finite-system/log-boltzmann-prob.md)

## Expansion

The finite positive partition sum $\sum_j\exp(-\Delta_fG_j'^\circ/RT)$ is $C^2$ in its arguments, so $g_i$ is $C^2$. Differentiating it at fixed $T$ gives $\partial g_i/\partial\,\mathrm{pH}=\sum_jr_j\,\partial\Delta_fG_j'^\circ/\partial\,\mathrm{pH}$, and $\partial\Delta_fG_j'^\circ/\partial\,\mathrm{pH}=RT\ln(10)N_{\mathrm H}(j)$ gives part 1. For part 2, $g_i/T=-R\ln\sum_j\exp(-\Delta_fG_j'^\circ/(RT))$, whose $T$-derivative is $\sum_jr_j\,\partial(\Delta_fG_j'^\circ/T)/\partial T$. Part 3 exchanges the order of the mixed partial derivatives of $g_i/T$ and of $g_i$ in $T$ and pH, using part 1. Part 4 exchanges the mixed partial derivatives of the $C^2$ function $g_i$ in pH and pMg, using part 1 and the magnesium-binding extension.

## Sources

- R. A. Alberty, A. Cornish-Bowden, R. N. Goldberg, G. G. Hammes, K. Tipton and H. V. Westerhoff, *Recommendations for terminology and databases for biochemical thermodynamics*, IUBMB Recommendations, Biophysical Chemistry 155 (2011) 89–103, <https://doi.org/10.1016/j.bpc.2011.03.007>. Equation numbers are those of the official IUBMB-hosted author manuscript (August 2010, 53 pages), <https://iubmb.qmul.ac.uk/thermod2/BiochemThermodynamics.pdf>: Section 5, equations (5-6)–(5-10) for parts 1 and 3, with (5-7) corrected as stated; Section 6, equations (6-7)–(6-10) for part 2 and the mean hydrogen count; Section 7, equation (7-13) for part 4.

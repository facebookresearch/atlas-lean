# Fundamental equation of the transformed Gibbs energy

At specified pH and pMg the free-ion terms drop out of the differential of the transformed Gibbs energy, and pH and pMg enter as natural variables whose conjugates are $RT\ln 10$ times the amounts of the hydrogen and magnesium components. Grouping species in equilibrium gives the same equation in reactant amounts.

**Setting.** Use the data and notation of the [transformed Gibbs energy](transformed-gibbs-energy-at-specified-ph-and-pmg.md), with the ionic strength $I$ fixed. Let $t\mapsto(T(t),P(t),\mathrm{pH}(t),\mathrm{pMg}(t),n(t))$ be a differentiable path of equilibrium states on an open interval, with $T(t)>0$, such that:

1. $G$ is differentiable along the path and satisfies the Gibbs fundamental equation

$$
\frac{dG}{dt}=-S\frac{dT}{dt}+V\frac{dP}{dt}+\sum_{j\in J}\mu_j\frac{dn_j}{dt};
$$

2. the free ions stay at the specified values: $\mu_{\mathrm{H^+}}(t)=\mu(\mathrm{H^+})(t)$ and $\mu_{\mathrm{Mg^{2+}}}(t)=\mu(\mathrm{Mg^{2+}})(t)$;
3. at the fixed $I$, $\Delta_fG^\circ(\mathrm{H^+})$ and $\Delta_fG^\circ(\mathrm{Mg^{2+}})$ are differentiable functions of $T$ alone (no pressure dependence).

Write $\bar S(\mathrm{H^+})=-\partial\mu(\mathrm{H^+})/\partial T$ at fixed pH, that is $\bar S(\mathrm{H^+})=-\frac{d}{dT}\Delta_fG^\circ(\mathrm{H^+})+R\ln(10)\,\mathrm{pH}$, define $\bar S(\mathrm{Mg^{2+}})$ in the same way with pMg, and let $S'=S-n_c(\mathrm H)\bar S(\mathrm{H^+})-n_c(\mathrm{Mg})\bar S(\mathrm{Mg^{2+}})$ be the transformed entropy.

**Statement.** Along the path,

$$
\frac{dG'}{dt}=-S'\frac{dT}{dt}+V\frac{dP}{dt}+\sum_{j\in J\setminus\{\mathrm{H^+},\mathrm{Mg^{2+}}\}}\mu_j'\frac{dn_j}{dt}+RT\ln(10)\,n_c(\mathrm H)\frac{d\,\mathrm{pH}}{dt}+RT\ln(10)\,n_c(\mathrm{Mg})\frac{d\,\mathrm{pMg}}{dt}.
$$

**Reactant form.** Suppose moreover that $J\setminus\{\mathrm{H^+},\mathrm{Mg^{2+}}\}$ is partitioned into finitely many groups (reactants) $J_i$, and that along the path all species of a group have one common transformed potential $\mu_i'$. With the reactant amounts $n_i'=\sum_{j\in J_i}n_j$ and $\Delta_fG_i'=\mu_i'$, the sum over species equals $\sum_i\Delta_fG_i'\,dn_i'/dt$. Then

$$
\frac{dG'}{dt}=-S'\frac{dT}{dt}+V\frac{dP}{dt}+\sum_i\Delta_fG_i'\frac{dn_i'}{dt}+RT\ln(10)\,n_c(\mathrm H)\frac{d\,\mathrm{pH}}{dt}+RT\ln(10)\,n_c(\mathrm{Mg})\frac{d\,\mathrm{pMg}}{dt},
$$

so at fixed $T$, $P$, pH, pMg and $I$ the rate of change of $G'$ involves only the changes of the reactant amounts. Here $n_c(\mathrm H)=n_{\mathrm{H^+}}+\sum_in_i'\bar N_{\mathrm H}(i)$, with $\bar N_{\mathrm H}(i)$ the amount-weighted mean hydrogen count of group $i$; the source writes $n_c(\mathrm H)=\sum_in_i'\bar N_{\mathrm H}(i)$, omitting the free hydrogen ions.

The source states, as the criterion for spontaneous change at specified $T$, $P$, pH, pMg, $I$ and reactant amounts, that $dG'\le0$; that criterion is a physical principle and is not part of this statement.

## Depends on

- [Transformed Gibbs energy at specified pH and pMg](transformed-gibbs-energy-at-specified-ph-and-pmg.md)

## Proof depends on

- [Transformed Gibbs energy at specified pH and pMg](transformed-gibbs-energy-at-specified-ph-and-pmg.md)

## Expansion

Differentiate $G'=G-n_c(\mathrm H)\mu(\mathrm{H^+})-n_c(\mathrm{Mg})\mu(\mathrm{Mg^{2+}})$ by the product rule. The terms $-\mu(\mathrm{H^+})\,dn_c(\mathrm H)/dt=-\sum_jN_{\mathrm H}(j)\mu(\mathrm{H^+})\,dn_j/dt$ and the magnesium analogue combine with $\sum_j\mu_j\,dn_j/dt$ into $\sum_j\mu_j'\,dn_j/dt$; by hypothesis 2 the coefficients $\mu'_{\mathrm{H^+}}$ and $\mu'_{\mathrm{Mg^{2+}}}$ vanish, so the free ions leave the sum. The remaining terms are $-n_c(\mathrm H)\,d\mu(\mathrm{H^+})/dt$ with $d\mu(\mathrm{H^+})/dt=-\bar S(\mathrm{H^+})\,dT/dt-RT\ln(10)\,d\,\mathrm{pH}/dt$ by hypothesis 3, and the magnesium analogue; they supply the transformed entropy and the pH and pMg terms. The reactant form only regroups the sum. Hypothesis 3 is the source's convention that the standard formation energies depend on temperature and ionic strength; a pressure dependence would add $-n_c(\mathrm H)\,\partial\mu(\mathrm{H^+})/\partial P$ to the volume coefficient.

## Sources

- R. A. Alberty, A. Cornish-Bowden, R. N. Goldberg, G. G. Hammes, K. Tipton and H. V. Westerhoff, *Recommendations for terminology and databases for biochemical thermodynamics*, IUBMB Recommendations, Biophysical Chemistry 155 (2011) 89–103, <https://doi.org/10.1016/j.bpc.2011.03.007>. Equation numbers are those of the official IUBMB-hosted author manuscript (August 2010, 53 pages), <https://iubmb.qmul.ac.uk/thermod2/BiochemThermodynamics.pdf>: equation (3-3) for the Gibbs fundamental equation; Section 5, equations (5-2), (5-4) and (5-5), the definition $S'=S-n_c(\mathrm H)S(\mathrm{H^+})$ and the criterion $(dG')\le0$; Section 7, equation (7-12) for the magnesium term.

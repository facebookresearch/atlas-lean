# Fundamental equation of the transformed Gibbs energy

At specified pH the free hydrogen-ion term drops out of the differential of the transformed Gibbs energy, and pH enters as a natural variable whose conjugate is $RT\ln 10$ times the amount of the hydrogen component. Grouping species in equilibrium gives the same equation in reactant amounts.

**Setting.** Use the data and notation of the [transformed Gibbs energy](transformed-gibbs-energy-at-specified-ph-and-pmg.md) in its pH-only variant, $G'=G-n_c(\mathrm H)\,\mu(\mathrm{H^+})$ and $\mu_j'=\mu_j-N_{\mathrm H}(j)\,\mu(\mathrm{H^+})$, with the ionic strength $I$ fixed. Any magnesium species, $\mathrm{Mg^{2+}}$ included, is then an ordinary member of $J$. Let $t\mapsto(T(t),P(t),\mathrm{pH}(t),n(t))$ be a differentiable path of equilibrium states on an open interval, with $T(t)>0$, such that:

1. $G$ is differentiable along the path and satisfies the Gibbs fundamental equation

$$
\frac{dG}{dt}=-S\frac{dT}{dt}+V\frac{dP}{dt}+\sum_{j\in J}\mu_j\frac{dn_j}{dt};
$$

2. the free hydrogen ion stays at the specified pH: $\mu_{\mathrm{H^+}}(t)=\mu(\mathrm{H^+})(t)$;
3. at the fixed $I$, $\Delta_fG^\circ(\mathrm{H^+})$ is a differentiable function of $T$ alone (no pressure dependence).

Write $\bar S(\mathrm{H^+})=-\partial\mu(\mathrm{H^+})/\partial T$ at fixed pH, that is $\bar S(\mathrm{H^+})=-\frac{d}{dT}\Delta_fG^\circ(\mathrm{H^+})+R\ln(10)\,\mathrm{pH}$, and let $S'=S-n_c(\mathrm H)\bar S(\mathrm{H^+})$ be the transformed entropy.

**Statement.** Then, along the path,

$$
\frac{dG'}{dt}=-S'\frac{dT}{dt}+V\frac{dP}{dt}+\sum_{j\in J\setminus\{\mathrm{H^+}\}}\mu_j'\frac{dn_j}{dt}+RT\ln(10)\,n_c(\mathrm H)\frac{d\,\mathrm{pH}}{dt}.
$$

**Reactant form.** Suppose moreover that $J\setminus\{\mathrm{H^+}\}$ is partitioned into finitely many groups (reactants) $J_i$, and that along the path all species of a group have one common transformed potential $\mu_i'$. With the reactant amounts $n_i'=\sum_{j\in J_i}n_j$ and $\Delta_fG_i'=\mu_i'$,

$$
\frac{dG'}{dt}=-S'\frac{dT}{dt}+V\frac{dP}{dt}+\sum_i\Delta_fG_i'\frac{dn_i'}{dt}+RT\ln(10)\,n_c(\mathrm H)\frac{d\,\mathrm{pH}}{dt},
$$

with $n_c(\mathrm H)=\sum_{j\in J}N_{\mathrm H}(j)\,n_j$ counting every hydrogen atom, those of the free hydrogen ions included. So at fixed $T$, $P$, pH and $I$ the rate of change of $G'$ involves only the changes of the reactant amounts.

The source states, as the criterion for spontaneous change at specified $T$, $P$, pH, $I$ and reactant amounts, that $dG'\le0$; that criterion is a physical principle and is not part of this statement.

## Derived extensions

These two statements are not printed in the source; each follows from the main statement's hypotheses and proof as shown.

**Magnesium term.** Use instead the transform with both reservoirs, $G'=G-n_c(\mathrm H)\mu(\mathrm{H^+})-n_c(\mathrm{Mg})\mu(\mathrm{Mg^{2+}})$, whose minus sign corrects the source's printed magnesium transform. Add to hypotheses 2 and 3 that the free magnesium ion stays at the specified pMg, $\mu_{\mathrm{Mg^{2+}}}(t)=\mu(\mathrm{Mg^{2+}})(t)$, and that $\Delta_fG^\circ(\mathrm{Mg^{2+}})$ is a differentiable function of $T$ alone. Let $\bar S(\mathrm{Mg^{2+}})=-\frac{d}{dT}\Delta_fG^\circ(\mathrm{Mg^{2+}})+R\ln(10)\,\mathrm{pMg}$, let $S'=S-n_c(\mathrm H)\bar S(\mathrm{H^+})-n_c(\mathrm{Mg})\bar S(\mathrm{Mg^{2+}})$, and let $\mathrm{pMg}(t)$ be differentiable. Then

$$
\frac{dG'}{dt}=-S'\frac{dT}{dt}+V\frac{dP}{dt}+\sum_{j\in J\setminus\{\mathrm{H^+},\mathrm{Mg^{2+}}\}}\mu_j'\frac{dn_j}{dt}+RT\ln(10)\,n_c(\mathrm H)\frac{d\,\mathrm{pH}}{dt}+RT\ln(10)\,n_c(\mathrm{Mg})\frac{d\,\mathrm{pMg}}{dt},
$$

and the reactant form holds with groups partitioning $J\setminus\{\mathrm{H^+},\mathrm{Mg^{2+}}\}$ and the extra pMg term. *Proof.* Repeat the main proof with the magnesium reservoir: $-\mu(\mathrm{Mg^{2+}})\,dn_c(\mathrm{Mg})/dt$ joins the species sum and makes the coefficient $\mu'_{\mathrm{Mg^{2+}}}$ vanish by the added hypothesis, and $-n_c(\mathrm{Mg})\,d\mu(\mathrm{Mg^{2+}})/dt$ with $d\mu(\mathrm{Mg^{2+}})/dt=-\bar S(\mathrm{Mg^{2+}})\,dT/dt-RT\ln(10)\,d\,\mathrm{pMg}/dt$ gives the entropy and pMg terms.

**Counting the hydrogen component by reactants.** In the reactant form, if every $n_i'>0$ and $\bar N_{\mathrm H}(i)=\sum_{j\in J_i}N_{\mathrm H}(j)\,n_j/n_i'$ is the amount-weighted mean hydrogen count of group $i$, then

$$
n_c(\mathrm H)=n_{\mathrm{H^+}}+\sum_in_i'\,\bar N_{\mathrm H}(i).
$$

*Proof.* Split $\sum_{j\in J}N_{\mathrm H}(j)n_j$ into the free-ion term, which is $1\cdot n_{\mathrm{H^+}}$, and the sums over the groups. The source's expression after its reactant fundamental equation, $n_c(\mathrm H)=\sum_in_i'\bar N_{\mathrm H}(i)$, omits the free hydrogen ions; the main statement does not use that expression.

## Depends on

- [Transformed Gibbs energy at specified pH and pMg](transformed-gibbs-energy-at-specified-ph-and-pmg.md)

## Proof depends on

- [Transformed Gibbs energy at specified pH and pMg](transformed-gibbs-energy-at-specified-ph-and-pmg.md)

## Expansion

Differentiate $G'=G-n_c(\mathrm H)\mu(\mathrm{H^+})$ by the product rule. The term $-\mu(\mathrm{H^+})\,dn_c(\mathrm H)/dt=-\sum_jN_{\mathrm H}(j)\mu(\mathrm{H^+})\,dn_j/dt$ combines with $\sum_j\mu_j\,dn_j/dt$ into $\sum_j\mu_j'\,dn_j/dt$; by hypothesis 2 the coefficient $\mu'_{\mathrm{H^+}}=\mu_{\mathrm{H^+}}-\mu(\mathrm{H^+})$ vanishes, so the free ion leaves the sum. The remaining term is $-n_c(\mathrm H)\,d\mu(\mathrm{H^+})/dt$ with $d\mu(\mathrm{H^+})/dt=-\bar S(\mathrm{H^+})\,dT/dt-RT\ln(10)\,d\,\mathrm{pH}/dt$ by hypothesis 3; it supplies the transformed entropy and the pH term. The reactant form only regroups the sum. Hypothesis 3 is the source's convention that the standard formation energies depend on temperature and ionic strength; a pressure dependence would add $-n_c(\mathrm H)\,\partial\mu(\mathrm{H^+})/\partial P$ to the volume coefficient.

## Sources

- R. A. Alberty, A. Cornish-Bowden, R. N. Goldberg, G. G. Hammes, K. Tipton and H. V. Westerhoff, *Recommendations for terminology and databases for biochemical thermodynamics*, IUBMB Recommendations, Biophysical Chemistry 155 (2011) 89–103, <https://doi.org/10.1016/j.bpc.2011.03.007>. Equation numbers are those of the official IUBMB-hosted author manuscript (August 2010, 53 pages), <https://iubmb.qmul.ac.uk/thermod2/BiochemThermodynamics.pdf>: equation (3-3) for the Gibbs fundamental equation; Section 5, equations (5-2), (5-4) and (5-5) for the main statement, the definition $S'=S-n_c(\mathrm H)S(\mathrm{H^+})$, the expression for $n_c(\mathrm H)$ after (5-5) and the criterion $(dG')\le0$; Section 7, equation (7-12) for the magnesium transform of the derived extension.

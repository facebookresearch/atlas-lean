# Coupling of biochemical reactions by an extra conserved component

Transformed reaction Gibbs energies add when biochemical reactions are added, but a sum alone does not impose coupling. Restricting two independent reaction directions to their sum adds one conserved component; the resulting energy budget can permit uphill conversion coupled to a larger downhill conversion.

**Setting.** Fix $T>0$, $P$, $I$, pH and pMg, and a finite set $I'$ of $N'$ reactants with composition matrix $A'$ as for the [apparent equilibrium constant](apparent-equilibrium-constant.md). Let $G'$ be a differentiable function of the reactant amounts $n'$ on an open set, with $\partial G'/\partial n_i'=\Delta_fG_i'$, as in the reactant form of the [fundamental equation of the transformed Gibbs energy](transformed-gibbs-fundamental-equation.md). For a biochemical reaction $\nu$ write $\Delta_rG'(\nu)=\sum_i\nu_i\Delta_fG_i'$ at the current state. Let $\nu_1,\nu_2\in\mathbb R^{I'}$ be linearly independent biochemical reactions, both [balanced](../../amounts-and-stoichiometry/balanced-reactions-and-stoichiometric-conservati/is-balanced.md) for $A'$. For a set $\mathcal S$ of reactions let $L(\mathcal S)=\{\ell\in\mathbb R^{I'}:\ell\cdot\nu=0\ \text{for all}\ \nu\in\mathcal S\}$ be the linear combinations of reactant amounts left unchanged by the [amounts after reaction extents](../../amounts-and-stoichiometry/balanced-reactions-and-stoichiometric-conservati/amount-after-extents.md) $n_0'+\sum_r\xi_r\nu_r$.

**Statement.**

1. (additivity) $\Delta_rG'(\nu_1+\nu_2)=\Delta_rG'(\nu_1)+\Delta_rG'(\nu_2)$, the same holds for $\Delta_rG'^\circ$, and $K'(\nu_1+\nu_2)=K'(\nu_1)\,K'(\nu_2)$.
2. (one more component) $\dim L(\{\nu_1,\nu_2\})=N'-2$ and $\dim L(\{\nu_1+\nu_2\})=N'-1$. A catalyst that carries out only $\nu_1+\nu_2$ leaves one more independent combination of reactant amounts unchanged than separate catalysis of $\nu_1$ and $\nu_2$.
3. (rates of change, wherever the composition lies in the open domain of $G'$) Along $n'(\xi_1,\xi_2)=n_0'+\xi_1\nu_1+\xi_2\nu_2$, $\partial G'/\partial\xi_k=\Delta_rG'(\nu_k)$; along $n'(\xi)=n_0'+\xi(\nu_1+\nu_2)$, $dG'/d\xi=\Delta_rG'(\nu_1)+\Delta_rG'(\nu_2)$.
4. (conditional energy budget) Assume the criterion that, at fixed $T$, $P$, pH, pMg and $I$, a composition change in an available direction $d$ can occur spontaneously only if $\nabla G'\cdot d\le0$. Forward progress along the combined direction requires $\Delta_rG'(\nu_1)+\Delta_rG'(\nu_2)\le0$, compatible with $\Delta_rG'(\nu_1)>0$ if $\Delta_rG'(\nu_2)\le-\Delta_rG'(\nu_1)$. In the two-direction model, $-\nu_1$ is a strict descent direction when $\Delta_rG'(\nu_1)>0$, but the sum direction can also decrease $G'$. The criterion is necessary only: neither a negative sum nor the existence of a descent direction identifies a coupling mechanism or determines a reaction rate.

The budget uses the transformed reaction Gibbs energies at the actual concentrations, not the standard values $\Delta_rG'^\circ$. Standard data for ATP hydrolysis and other cofactor reactions enter as functions of $T$, $I$, pH and pMg, not as fixed energies.

**Example.** For glutamate–ammonia ligase, $\mathrm{ATP}+\text{glutamate}+\text{ammonia}=\mathrm{ADP}+\text{phosphate}+\text{glutamine}$ is the sum of $\mathrm{ATP}+\mathrm{H_2O}=\mathrm{ADP}+\text{phosphate}$ and $\text{glutamate}+\text{ammonia}=\text{glutamine}+\mathrm{H_2O}$, and water cancels. Over C, N, O and P the six reactants of the combined reaction have a composition matrix of rank $4$. With the apparent equilibrium constant that gives five relations for six concentrations. The missing relation is the extra component: the amount of ATP plus the amount of glutamine is conserved by the combined reaction, but not by ATP hydrolysis alone, and it is no combination of element balances.

## Depends on

- [Apparent equilibrium constant and transformed reaction Gibbs energy](apparent-equilibrium-constant.md)
- [Fundamental equation of the transformed Gibbs energy](transformed-gibbs-fundamental-equation.md)
- [Balanced reaction for a composition matrix](../../amounts-and-stoichiometry/balanced-reactions-and-stoichiometric-conservati/is-balanced.md)
- [Amounts after advancing reactions by given extents](../../amounts-and-stoichiometry/balanced-reactions-and-stoichiometric-conservati/amount-after-extents.md)

## Proof depends on

- [Apparent equilibrium constant and transformed reaction Gibbs energy](apparent-equilibrium-constant.md)
- [Fundamental equation of the transformed Gibbs energy](transformed-gibbs-fundamental-equation.md)
- [Amounts after advancing reactions by given extents](../../amounts-and-stoichiometry/balanced-reactions-and-stoichiometric-conservati/amount-after-extents.md)
- [Hess's law for linear combinations of reactions](../thermochemistry-and-hess-s-law/hess-law.md), applied to the linear functional $\nu\mapsto\sum_i\nu_i\Delta_fG_i'$

## Expansion

Part 1: $\nu\mapsto\sum_i\nu_i\Delta_fG_i'$ is linear, which is Hess's law with the molar values $\Delta_fG_i'$ (or $\Delta_fG_i'^\circ$) in place of molar enthalpies; exponentiate for $K'$. Part 2: $L(\mathcal S)$ is the orthogonal complement of the span of $\mathcal S$, of dimension $N'$ minus the rank, and the rank is $2$ for independent $\nu_1,\nu_2$ and $1$ for $\nu_1+\nu_2\ne0$. Part 3 is the chain rule with $\partial G'/\partial n_i'=\Delta_fG_i'$. Part 4 applies the criterion to $d=\nu_1+\nu_2$ in the coupled case and to $d=-\nu_1$ in the uncoupled case, where $\nabla G'\cdot(-\nu_1)=-\Delta_rG'(\nu_1)<0$. The example's arithmetic uses element counts C10 N5 O13 P3 for ATP, C10 N5 O10 P2 for ADP, O4 P for phosphate, C5 N O4 for glutamate, N for ammonia, C5 N2 O3 for glutamine and O for water, with hydrogen not conserved at specified pH.

## Sources

- R. A. Alberty, A. Cornish-Bowden, R. N. Goldberg, G. G. Hammes, K. Tipton and H. V. Westerhoff, *Recommendations for terminology and databases for biochemical thermodynamics*, IUBMB Recommendations, Biophysical Chemistry 155 (2011) 89–103, <https://doi.org/10.1016/j.bpc.2011.03.007>. Equation numbers are those of the official IUBMB-hosted author manuscript (August 2010, 53 pages), <https://iubmb.qmul.ac.uk/thermod2/BiochemThermodynamics.pdf>: Section 2, equations (2-8)–(2-10) and the discussion of components; Section 5, the criterion $(dG')\le0$ after equation (5-5); Section 7, equations (7-2)–(7-4) and (7-7); Section 8, equations (8-10) and (8-11), $N'=C'+R'$, and the remark that coupling by the enzyme mechanism adds components.

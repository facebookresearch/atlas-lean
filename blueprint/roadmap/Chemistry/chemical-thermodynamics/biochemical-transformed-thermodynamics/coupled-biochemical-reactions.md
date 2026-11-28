# Coupling of biochemical reactions by an extra conserved component

Transformed reaction Gibbs energies add when biochemical reactions are added, but only a mechanism that runs the sum couples them. Glutamate–ammonia ligase runs ATP hydrolysis and glutamine synthesis as one reaction: its transformed Gibbs energy is the sum of theirs, and it conserves one quantity beyond the element balances.

**Setting.** Fix $T>0$, $P$, $I$ and pH, and take as reactants $I'$ ATP, ADP, phosphate, glutamate, ammonia, glutamine and water, with composition matrix $A'$ over C, N, O and P as for the [apparent equilibrium constant](apparent-equilibrium-constant.md); hydrogen is not balanced at specified pH. Consider the biochemical reactions

$$
\nu_a:\ \mathrm{ATP}+\mathrm{H_2O}=\mathrm{ADP}+\text{phosphate},\qquad \nu_b:\ \text{glutamate}+\text{ammonia}=\text{glutamine}+\mathrm{H_2O},
$$

$$
\nu_c=\nu_a+\nu_b:\ \mathrm{ATP}+\text{glutamate}+\text{ammonia}=\mathrm{ADP}+\text{phosphate}+\text{glutamine},
$$

each [balanced](../../amounts-and-stoichiometry/balanced-reactions-and-stoichiometric-conservati/is-balanced.md) for $A'$; water cancels in $\nu_c$. Let $G'$ be a differentiable function of the reactant amounts $n'$ on an open set, with $\partial G'/\partial n_i'=\Delta_fG_i'$, as in the reactant form of the [fundamental equation of the transformed Gibbs energy](transformed-gibbs-fundamental-equation.md), and write $\Delta_rG'(\nu)=\sum_i\nu_i\Delta_fG_i'$ at the current state.

**Statement.**

1. (additivity) $\Delta_rG'(\nu_c)=\Delta_rG'(\nu_a)+\Delta_rG'(\nu_b)$, the same holds for the standard values $\Delta_rG'^\circ$, and $K'(\nu_c)=K'(\nu_a)\,K'(\nu_b)$.
2. (single extent) Along the [amounts after an extent](../../amounts-and-stoichiometry/balanced-reactions-and-stoichiometric-conservati/amount-after-extents.md) $n'(\xi')=n_0'+\xi'\nu_c$ of the ligase reaction, wherever $n'(\xi')$ lies in the domain of $G'$,

$$
\frac{dG'}{d\xi'}=\Delta_rG'(\nu_c)=\Delta_rG'(\nu_a)+\Delta_rG'(\nu_b).
$$

Under the source's criterion that a biochemical reaction can go spontaneously to the right only if its transformed reaction Gibbs energy at the actual concentrations is negative, the ligase reaction can run forward only when $\Delta_rG'(\nu_a)+\Delta_rG'(\nu_b)<0$, a condition compatible with $\Delta_rG'(\nu_b)>0$.

3. (extra component) The composition matrix of the six reactants of $\nu_c$ over C, N, O and P has rank $4$, while the linear combinations of their amounts left unchanged by $\nu_c$ form a space of dimension $5$. So the ligase reaction conserves one combination of reactant amounts that is no combination of element balances. With the apparent equilibrium constant, the element balances give only five relations among six equilibrium concentrations; the extra conserved combination supplies the sixth.

The energies in part 2 are those at the actual concentrations, not the standard values. Standard data for ATP hydrolysis enter as functions of $T$, $I$ and pH, not as fixed energies.

## Derived extensions

These statements are not printed in the source; each is proved here.

**The extra conserved quantity.** The amount of ATP plus the amount of glutamine is conserved by $\nu_c$ but changed by $\nu_a$, and it is not in the row space of $A'$. *Proof.* $\nu_c$ changes ATP by $-1$ and glutamine by $+1$, $\nu_a$ changes ATP by $-1$ and glutamine by $0$, and a combination of the C, N, O, P rows with weight $0$ on ADP, phosphate, glutamate and ammonia is zero: ammonia forces the N weight to $0$, glutamate and phosphate then fix the C and P weights as multiples of the O weight, and ADP forces the O weight to $0$. Such a combination gives ATP weight $0$, not $1$.

**General component count.** For any finite set of $N'$ reactants and linearly independent biochemical reactions $\nu_1,\nu_2$, let $L(\mathcal S)=\{\ell:\ell\cdot\nu=0\ \text{for all}\ \nu\in\mathcal S\}$. Then $\dim L(\{\nu_1,\nu_2\})=N'-2$ and $\dim L(\{\nu_1+\nu_2\})=N'-1$: running only the sum conserves exactly one more independent combination than running both reactions separately. *Proof.* $L(\mathcal S)$ is the orthogonal complement of the span of $\mathcal S$, whose dimension is $2$ for independent $\nu_1,\nu_2$ and $1$ for $\nu_1+\nu_2\ne0$.

**Conditional energy budget.** In the general setting, assume that a composition change in an available direction $d$ can occur spontaneously only if $\nabla G'\cdot d\le0$. Along $n_0'+\xi_1\nu_1+\xi_2\nu_2$, $\partial G'/\partial\xi_k=\Delta_rG'(\nu_k)$. If only $\nu_1+\nu_2$ is available, forward progress requires $\Delta_rG'(\nu_1)+\Delta_rG'(\nu_2)\le0$, compatible with $\Delta_rG'(\nu_1)>0$. If both directions are available and $\Delta_rG'(\nu_1)>0$, then $-\nu_1$ is a direction of strict decrease. The criterion is necessary only: neither a negative sum nor a descent direction identifies a coupling mechanism or fixes a rate. *Proof.* The chain rule with $\partial G'/\partial n_i'=\Delta_fG_i'$, and $\nabla G'\cdot(-\nu_1)=-\Delta_rG'(\nu_1)$.

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

Part 1: $\nu\mapsto\sum_i\nu_i\Delta_fG_i'$ is linear, which is Hess's law with the molar values $\Delta_fG_i'$ (or $\Delta_fG_i'^\circ$) in place of molar enthalpies; exponentiate for $K'$. Part 2 is the chain rule with $\partial G'/\partial n_i'=\Delta_fG_i'$, followed by part 1. Part 3 uses the element counts C10 N5 O13 P3 for ATP, C10 N5 O10 P2 for ADP, O4 P for phosphate, C5 N O4 for glutamate, N for ammonia and C5 N2 O3 for glutamine: the columns of ADP, phosphate, ammonia and glutamine are independent, so the rank is $4$, and the space conserved by the single nonzero reaction $\nu_c$ in six amounts has dimension $6-1=5$. The extra conserved combination is the derived extension above.

## Sources

- R. A. Alberty, A. Cornish-Bowden, R. N. Goldberg, G. G. Hammes, K. Tipton and H. V. Westerhoff, *Recommendations for terminology and databases for biochemical thermodynamics*, IUBMB Recommendations, Biophysical Chemistry 155 (2011) 89–103, <https://doi.org/10.1016/j.bpc.2011.03.007>. Equation numbers are those of the official IUBMB-hosted author manuscript (August 2010, 53 pages), <https://iubmb.qmul.ac.uk/thermod2/BiochemThermodynamics.pdf>: Section 2, equations (2-8)–(2-10) and the discussion of the additional conservation relationship; Section 7, equations (7-2)–(7-4) and (7-7) with the statement that the sign of the transformed reaction Gibbs energy determines the direction; Section 8, equations (8-10) and (8-11), $N'=C'+R'$, and the remark that coupling by the enzyme mechanism adds components.

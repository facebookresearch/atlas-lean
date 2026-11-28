# Molar reaction Gibbs energy and its standard value

The molar reaction Gibbs energy of a reaction is $\Delta_rG=\sum_i\nu_i\mu_i$ and its standard value is $\Delta_rG^\circ=\sum_i\nu_i\mu_i^\circ$, both per unit advancement of the reaction as written.

For a reaction with stoichiometric numbers $\nu_i$ (positive for products, negative for reactants) among
species with chemical potentials $\mu_i$ (in the activity form of
[the chemical potential](chemical-potential-in-terms-of-relative-activity.md)), the **molar reaction Gibbs
energy** is

$$\Delta_rG=\sum_i\nu_i\mu_i ,$$

and, with standard chemical potentials $\mu_i^\circ$ (functions of $T$ for chosen standard states), the
**standard molar reaction Gibbs energy** is

$$\Delta_rG^\circ=\sum_i\nu_i\mu_i^\circ .$$

Both are per unit advancement (J mol$^{-1}$) and so depend on how the reaction equation is written: scaling
every $\nu_i$ by $c$ scales both by $c$. $\Delta_rG^\circ$ depends only on $T$ and the standard states.
$-\Delta_rG$ is the affinity of the reaction.

## Context

Undergraduate chemical thermodynamics. In a galvanic cell the chemical potentials of ions are taken at the electric potential of their own phase; this gives the molar reaction Gibbs energy of the cell reaction.

## Depends on

- [Chemical potential in terms of relative activity](chemical-potential-in-terms-of-relative-activity.md)

## Proof depends on

None.

## Expansion

A definition. Interpretation (not part of the definition): for a closed system whose amounts change only through this reaction, $n_i=n_i^{(0)}+\nu_i\xi$ ([amounts after advancing by an extent](../../amounts-and-stoichiometry/balanced-reactions-and-stoichiometric-conservati/amount-after-extents.md)), and if $G(T,p,n)$ is differentiable with $\mu_i=\partial G/\partial n_i$ at fixed $T,p$ and other amounts, the chain rule gives $\Delta_rG=(\partial G/\partial\xi)_{T,p}$ and $dG=-S\,dT+V\,dp+\Delta_rG\,d\xi$ (DeVoe Eqs. 11.7.1–11.7.3).

## Sources

- H. DeVoe, *Thermodynamics and Chemistry*, 2nd edition, Chemistry LibreTexts edition, Section 11.8.1, Eq. 11.8.3 (standard molar reaction Gibbs energy), with $\Delta_rG=\sum_i\nu_i\mu_i$ as used in Eq. 11.8.2. [Section 11.8.1](https://chem.libretexts.org/Bookshelves/Physical_and_Theoretical_Chemistry_Textbook_Maps/DeVoes_Thermodynamics_and_Chemistry/11%3A_Reactions_and_Other_Chemical_Processes/11.08%3A_The_Thermodynamic_Equilibrium_Constant)
- H. DeVoe, *Thermodynamics and Chemistry*, 2nd edition, Chemistry LibreTexts edition, Section 11.7, Eqs. 11.7.1–11.7.3 (derivative with respect to the advancement in a closed system) and the definition of the affinity. [Section 11.7](https://chem.libretexts.org/Bookshelves/Physical_and_Theoretical_Chemistry_Textbook_Maps/DeVoes_Thermodynamics_and_Chemistry/11%3A_Reactions_and_Other_Chemical_Processes/11.07%3A_Gibbs_Energy_and_Reaction_Equilibrium)

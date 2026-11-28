# Reaction Gibbs energy from the reaction quotient

If charge is conserved and every ion is at the same electric potential, the molar reaction Gibbs energy is $\Delta_rG=\Delta_rG^\circ+RT\ln Q_{\mathrm{rxn}}$, independent of that potential.

Let $T>0$, let a reaction have stoichiometric numbers $\nu_i$ and let each species $i$ have charge number
$z_i$, standard chemical potential $\mu_i^\circ$ and relative activity $a_i>0$, so that
$\mu_i=\mu_i^\circ+RT\ln a_i+z_iF\phi_i$. Suppose

1. charge is conserved, $\sum_i\nu_iz_i=0$ (the reaction is [balanced](../../amounts-and-stoichiometry/balanced-reactions-and-stoichiometric-conservati/is-balanced.md) for a balance coordinate
   equal to the charge number), and
2. every charged reactant and product is in a phase of the same electric potential $\phi_i=\phi'$.

Then

$$\Delta_rG=\Delta_rG^\circ+RT\ln Q_{\mathrm{rxn}},$$

with $\Delta_rG$, $\Delta_rG^\circ$ the [molar reaction Gibbs energy and its standard value](molar-reaction-gibbs-energy.md)
and $Q_{\mathrm{rxn}}$ the [reaction quotient](reaction-quotient-and-equilibrium-constant.md). In particular
$\Delta_rG$ depends only on $T$ and the activities, not on $\phi'$. Without hypothesis 2 the identity fails
in general; a galvanic cell is the case where ions sit at different potentials.

## Context

Undergraduate chemical thermodynamics (DeVoe's Eq. 11.8.8). It is the step from which the Nernst equation follows once the reaction Gibbs energy of a cell reaction is tied to the cell potential.

## Depends on

- [Chemical potential in terms of relative activity](chemical-potential-in-terms-of-relative-activity.md)
- [Molar reaction Gibbs energy and its standard value](molar-reaction-gibbs-energy.md)
- [Reaction quotient and thermodynamic equilibrium constant](reaction-quotient-and-equilibrium-constant.md)
- [Balanced reaction for a composition matrix](../../amounts-and-stoichiometry/balanced-reactions-and-stoichiometric-conservati/is-balanced.md)

## Proof depends on

None.

## Expansion

Substitute the activity form of $\mu_i$ into $\Delta_rG=\sum\nu_i\mu_i$: $\Delta_rG=\sum\nu_i\mu_i^\circ+RT\sum\nu_i\ln a_i+F\phi'\sum\nu_iz_i$ (DeVoe Eq. 11.8.2). The last sum vanishes by charge conservation, the first is $\Delta_rG^\circ$ and the middle one is $RT\ln Q_{\mathrm{rxn}}$.

## Sources

- H. DeVoe, *Thermodynamics and Chemistry*, 2nd edition, Chemistry LibreTexts edition, Section 11.8.1, Eqs. 11.8.2, 11.8.4, 11.8.5 and 11.8.8. [Section 11.8.1](https://chem.libretexts.org/Bookshelves/Physical_and_Theoretical_Chemistry_Textbook_Maps/DeVoes_Thermodynamics_and_Chemistry/11%3A_Reactions_and_Other_Chemical_Processes/11.08%3A_The_Thermodynamic_Equilibrium_Constant)

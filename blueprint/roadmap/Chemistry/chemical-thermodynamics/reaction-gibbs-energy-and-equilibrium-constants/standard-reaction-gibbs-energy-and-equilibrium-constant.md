# Standard reaction Gibbs energy and the equilibrium constant

At a state of zero affinity ($\Delta_rG=0$, DeVoe's criterion of reaction equilibrium) the reaction quotient equals $\exp(-\Delta_rG^\circ/RT)$; so $K=\exp(-\Delta_rG^\circ/RT)$ depends only on $T$ and the standard states, and $K>1$ exactly when $\Delta_rG^\circ<0$.

Assume the hypotheses of [the reaction Gibbs energy from the reaction quotient](reaction-gibbs-energy-from-the-reaction-quotient.md):
$T>0$, charge conservation $\sum_i\nu_iz_i=0$, and all ions at one electric potential. Call a state one of
**zero affinity** if $\Delta_rG=0$; DeVoe's criterion of reaction equilibrium (Eq. 11.7.4) is exactly this
condition for a reaction that can advance in both directions. Then, at temperature $T$ and for fixed standard
states:

1. a state has zero affinity if and only if $Q_{\mathrm{rxn}}=\exp(-\Delta_rG^\circ/RT)$;
2. hence every state of reaction equilibrium has the same quotient, and the
   [equilibrium constant](reaction-quotient-and-equilibrium-constant.md) is

$$K=\exp\!\Big(-\frac{\Delta_rG^\circ}{RT}\Big),\qquad \Delta_rG^\circ=-RT\ln K,$$

a function of $T$ alone (neither pressure nor composition changes it);

3. $K>1$ if and only if $\Delta_rG^\circ<0$, and $K<1$ if and only if $\Delta_rG^\circ>0$.

$\Delta_rG^\circ$ and $K$ must use the same standard states. Zero affinity is a stationarity condition: the
statement does not claim that a state with $Q_{\mathrm{rxn}}=K$ is a minimum of the Gibbs energy.

## Context

Undergraduate chemical thermodynamics. Combined with $\Delta_rG^\circ=-zFE^\circ$ it gives the electrochemical route to equilibrium constants.

## Depends on

- [Reaction quotient and thermodynamic equilibrium constant](reaction-quotient-and-equilibrium-constant.md)
- [Molar reaction Gibbs energy and its standard value](molar-reaction-gibbs-energy.md)

## Proof depends on

- [Reaction Gibbs energy from the reaction quotient](reaction-gibbs-energy-from-the-reaction-quotient.md)

## Expansion

By the identity $\Delta_rG=\Delta_rG^\circ+RT\ln Q_{\mathrm{rxn}}=RT\ln\big(Q_{\mathrm{rxn}}e^{\Delta_rG^\circ/RT}\big)$, $\Delta_rG=0$ exactly when $Q_{\mathrm{rxn}}=e^{-\Delta_rG^\circ/RT}$ (DeVoe Eqs. 11.8.8, 11.8.10, 11.8.11). Since $\Delta_rG^\circ$ depends only on $T$, so does $K$; the sign statements are monotonicity of $\exp$.

## Sources

- H. DeVoe, *Thermodynamics and Chemistry*, 2nd edition, Chemistry LibreTexts edition, Section 11.8.1, Eqs. 11.8.8, 11.8.10 and 11.8.11 and the following discussion. [Section 11.8.1](https://chem.libretexts.org/Bookshelves/Physical_and_Theoretical_Chemistry_Textbook_Maps/DeVoes_Thermodynamics_and_Chemistry/11%3A_Reactions_and_Other_Chemical_Processes/11.08%3A_The_Thermodynamic_Equilibrium_Constant)
- H. DeVoe, *Thermodynamics and Chemistry*, 2nd edition, Chemistry LibreTexts edition, Section 11.7, Eq. 11.7.4 (reaction equilibrium: $\Delta_rG=0$) and the affinity of reaction. [Section 11.7](https://chem.libretexts.org/Bookshelves/Physical_and_Theoretical_Chemistry_Textbook_Maps/DeVoes_Thermodynamics_and_Chemistry/11%3A_Reactions_and_Other_Chemical_Processes/11.07%3A_Gibbs_Energy_and_Reaction_Equilibrium)

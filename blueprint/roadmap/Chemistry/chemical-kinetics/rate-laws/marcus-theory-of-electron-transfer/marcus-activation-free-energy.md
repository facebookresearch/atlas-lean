# Marcus activation free energy

In the two-parabola model the free-energy curves cross at a single configuration, and the activation free energy measured from the donor minimum is $\Delta G^\ddagger=(\Delta G^\circ+\lambda)^2/(4\lambda)$.

In the [Marcus two-parabola model](marcus-two-parabola-model.md) with $\lambda>0$, the equation $G_D(q)=G_A(q)$ has exactly one
solution,

$$d_C=\frac{\Delta G^\circ}{2\lambda}(d_A-d_D)+\frac{d_A+d_D}{2},$$

and the activation free energy $\Delta G^\ddagger=G_D(d_C)-G_D(d_D)$ is

$$\Delta G^\ddagger=\frac{(\Delta G^\circ+\lambda)^2}{4\lambda}=\frac\lambda4\Big(1+\frac{\Delta G^\circ}{\lambda}\Big)^2 .$$

Thus $\Delta G^\ddagger\ge0$, with $\Delta G^\ddagger=0$ exactly when $-\Delta G^\circ=\lambda$; for a self-exchange
reaction ($\Delta G^\circ=0$) $\Delta G^\ddagger=\lambda/4$.

## Context

Graduate physical chemistry; the central formula of Marcus theory. With electrostatic work terms $w^r,w^p$ for bimolecular reactions, $\Delta G^\circ$ is replaced by $\Delta G^\circ+w^p-w^r$ and $w^r$ is added to the barrier.

## Depends on

- [Marcus two-parabola model and the reorganization energy](marcus-two-parabola-model.md)

## Proof depends on

None.

## Expansion

$G_A-G_D=\tfrac12m\omega_0^2[(d_A^2-d_D^2)-2q(d_A-d_D)]+\Delta G^\circ$ is affine in $q$ with nonzero slope, so it has one zero; solving and using $\lambda=\tfrac12m\omega_0^2(d_A-d_D)^2$ gives $d_C$ (Tokmakoff Eq. 19.4.4). Then $d_C-d_D=(d_A-d_D)(\Delta G^\circ+\lambda)/(2\lambda)$ and $\Delta G^\ddagger=\lambda(\Delta G^\circ+\lambda)^2/(4\lambda^2)$ (Eq. 19.4.5).

## Sources

- A. Tokmakoff, *Time-Dependent Quantum Mechanics and Spectroscopy*, Chemistry LibreTexts edition, Section 19.4 (Marcus Theory for Electron Transfer), Eqs. 19.4.4–19.4.5. [Section 19.4](https://chem.libretexts.org/Bookshelves/Physical_and_Theoretical_Chemistry_Textbook_Maps/Time-Dependent_Quantum_Mechanics_and_Spectroscopy_2025e_%28Tokmakoff%29/19%3A_Energy_and_Charge_Transfer/19.04%3A_Marcus_Theory_for_Electron_Transfer)
- I. Bertini, H. B. Gray, S. J. Lippard and J. S. Valentine, *Bioinorganic Chemistry*, University Science Books, 1994, Chemistry LibreTexts edition, Section 6.8 (Marcus Theory), Eqs. 6.17–6.18 (barrier with work terms). [Section 6.8](https://chem.libretexts.org/Bookshelves/Inorganic_Chemistry/Book3A_Bioinorganic_Chemistry_%28Bertini_et_al.%29/06%3A_Electron_Transfer/6.08%3A_Marcus_Theory)

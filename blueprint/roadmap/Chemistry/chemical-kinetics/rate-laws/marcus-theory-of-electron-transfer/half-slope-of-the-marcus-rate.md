# Half-slope of the Marcus rate at small driving force

At zero reaction free energy the logarithmic Marcus rate ratio $\ln(k/k(0))$ has slope one half against the dimensionless driving force $u=-\Delta G^\circ/k_BT$: $\ln(k/k(0))=\tfrac12u+O(u^2)$, the microscopic counterpart of a symmetric transfer coefficient.

Let $A,\lambda,k_BT>0$ be fixed and $k(\Delta G^\circ)=A\exp(-(\Delta G^\circ+\lambda)^2/(4\lambda k_BT))$, the
[Marcus rate](marcus-inverted-region.md). Then

$$\ln k(\Delta G^\circ)=\ln k(0)-\frac{\Delta G^\circ}{2k_BT}-\frac{(\Delta G^\circ)^2}{4\lambda k_BT}\qquad\text{exactly, with }k(0)=Ae^{-\lambda/(4k_BT)},$$

so with the dimensionless driving force $u=-\Delta G^\circ/k_BT$,

$$\ln\frac{k}{k(0)}=\frac12u-\frac{k_BT}{4\lambda}u^2 :$$

the logarithmic rate ratio has slope $\tfrac12$ against $u$ at $u=0$, and the quadratic term is small compared with
the linear one for $|\Delta G^\circ|\ll\lambda$.

## Context

Graduate physical chemistry. Marcus noted the slope one half for small free energies of reaction and the analogous behaviour at electrodes, where the reaction free energy is replaced by the transferred charge times the activation overpotential; it is the microscopic counterpart of a symmetric Butler–Volmer transfer coefficient near equilibrium. The slope-$\tfrac12$ dependence of $\ln k_{12}$ on $\ln K_{12}$ in the [cross relation](marcus-cross-relation.md) is the same effect.

## Depends on

- [Marcus rate and the inverted region](marcus-inverted-region.md)

## Proof depends on

None.

## Expansion

Expand $(\Delta G^\circ+\lambda)^2=\lambda^2+2\lambda\Delta G^\circ+(\Delta G^\circ)^2$ and divide by $4\lambda k_BT$. Substituting $\Delta G^\circ=-k_BTu$ gives the form in $u$. Away from $u=0$ the derivative of the same expression, $\tfrac12+\Delta G^\circ/(2\lambda)$ in these units, is model algebra; the sourced statement is the slope one half at small $\Delta G^\circ$ (Nobel lecture, p. 85).

## Sources

- R. A. Marcus, Electron transfer reactions in chemistry: theory and experiment, Nobel Lecture, 8 December 1992, p. 85, consequence of Eq. (5): linear dependence of $\ln k$ on $-\Delta G^\circ$ with a slope of 1/2 when $\Delta G^\circ$ is small, a similar behaviour at electrodes, and the curvature of $\ln k$ plots. [Nobel Lecture PDF](https://www.nobelprize.org/uploads/2018/06/marcus-lecture.pdf)
- A. Tokmakoff, *Time-Dependent Quantum Mechanics and Spectroscopy*, Chemistry LibreTexts edition, Section 19.4 (Marcus Theory for Electron Transfer), Eq. 19.4.6. [Section 19.4](https://chem.libretexts.org/Bookshelves/Physical_and_Theoretical_Chemistry_Textbook_Maps/Time-Dependent_Quantum_Mechanics_and_Spectroscopy_2025e_%28Tokmakoff%29/19%3A_Energy_and_Charge_Transfer/19.04%3A_Marcus_Theory_for_Electron_Transfer)
- I. Bertini, H. B. Gray, S. J. Lippard and J. S. Valentine, *Bioinorganic Chemistry*, University Science Books, 1994, Chemistry LibreTexts edition, Section 6.8 (Marcus Theory), discussion after Eq. 6.26 (slope 0.5 of $\ln k_{12}$ against $\ln K_{12}$ in the normal region). [Section 6.8](https://chem.libretexts.org/Bookshelves/Inorganic_Chemistry/Book3A_Bioinorganic_Chemistry_%28Bertini_et_al.%29/06%3A_Electron_Transfer/6.08%3A_Marcus_Theory)

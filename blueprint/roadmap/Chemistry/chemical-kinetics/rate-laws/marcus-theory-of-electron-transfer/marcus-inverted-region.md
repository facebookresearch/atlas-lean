# Marcus rate and the inverted region

With a fixed prefactor, the Marcus rate $k=A\exp(-(\Delta G^\circ+\lambda)^2/(4\lambda k_BT))$ increases with the driving force $-\Delta G^\circ$ up to its maximum $A$ at $-\Delta G^\circ=\lambda$ and then decreases: the inverted region.

Let $A>0$, $\lambda>0$ and $k_BT>0$ be fixed, and let the electron-transfer rate constant be the activated rate over
the [Marcus barrier](marcus-activation-free-energy.md),

$$k(\Delta G^\circ)=A\exp\!\Big(-\frac{\Delta G^\ddagger}{k_BT}\Big)=A\exp\!\Big(-\frac{(\Delta G^\circ+\lambda)^2}{4\lambda k_BT}\Big).$$

In terms of the driving force $D=-\Delta G^\circ$, write $k_{\mathrm{drive}}(D)=k(-D)=A\exp(-(\lambda-D)^2/(4\lambda k_BT))$.
Then $k_{\mathrm{drive}}$ is strictly increasing on $(-\infty,\lambda]$ (the normal region), attains its maximum
value $A$ exactly at $D=\lambda$ (activationless transfer), and is strictly decreasing on $[\lambda,\infty)$ (the
inverted region): in the inverted region a more exergonic reaction is slower. Equivalently $k$ is symmetric about
$\Delta G^\circ=-\lambda$, $k(-\lambda+s)=k(-\lambda-s)$, and $k_{\mathrm{drive}}(\lambda+s)=k_{\mathrm{drive}}(\lambda-s)$ for all real $s$:
$\ln k$ is a downward parabola in $\Delta G^\circ$.

## Context

Graduate physical chemistry. The inverted region, predicted by Marcus in 1960, was confirmed by Miller, Calcaterra and Closs in 1984. In the uniform-density-of-states model of electron transfer at a metal electrode it disappears ([saturation of the Marcus–Hush–Chidsey rate](../../electrode-kinetics/marcus-hush-chidsey-rate-saturates.md)).

## Depends on

- [Marcus activation free energy](marcus-activation-free-energy.md)

## Proof depends on

None.

## Expansion

$\ln k_{\mathrm{drive}}=\ln A-(\lambda-D)^2/(4\lambda k_BT)$ is a strictly concave quadratic in $D$ with vertex at $D=\lambda$; monotonicity on each side and symmetry about the vertex follow, and the statements in $\Delta G^\circ$ follow by $\Delta G^\circ=-D$ (Tokmakoff discussion after Eq. 19.4.6; Bertini Fig. 6.23).

## Sources

- A. Tokmakoff, *Time-Dependent Quantum Mechanics and Spectroscopy*, Chemistry LibreTexts edition, Section 19.4 (Marcus Theory for Electron Transfer), Eq. 19.4.6 and the discussion of the maximum at $-\Delta G^\circ=\lambda$; also Eq. 19.4.28 and the inverted regime. [Section 19.4](https://chem.libretexts.org/Bookshelves/Physical_and_Theoretical_Chemistry_Textbook_Maps/Time-Dependent_Quantum_Mechanics_and_Spectroscopy_2025e_%28Tokmakoff%29/19%3A_Energy_and_Charge_Transfer/19.04%3A_Marcus_Theory_for_Electron_Transfer)
- I. Bertini, H. B. Gray, S. J. Lippard and J. S. Valentine, *Bioinorganic Chemistry*, University Science Books, 1994, Chemistry LibreTexts edition, Section 6.8 (Marcus Theory), Eq. 6.21 and the normal, activationless and inverted regions (Fig. 6.23). [Section 6.8](https://chem.libretexts.org/Bookshelves/Inorganic_Chemistry/Book3A_Bioinorganic_Chemistry_%28Bertini_et_al.%29/06%3A_Electron_Transfer/6.08%3A_Marcus_Theory)
- R. A. Marcus, Electron transfer reactions in chemistry: theory and experiment, Nobel Lecture, 8 December 1992, discussion of the inverted region following Eq. (5b) and its experimental confirmation (Miller, Calcaterra and Closs, 1984). [Nobel Lecture PDF](https://www.nobelprize.org/uploads/2018/06/marcus-lecture.pdf)

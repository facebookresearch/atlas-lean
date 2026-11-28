# Nonadiabatic Marcus electron-transfer rate

For weakly coupled donor and acceptor states and a classical, short-time treatment of the nuclear modes, the golden-rule electron-transfer rate is approximated by $w_{\mathrm{ET}}=\frac{|J_{AD}|^2}{\hbar}\sqrt{\frac{\pi}{\lambda k_BT}}\exp\!\big(-\frac{(\Delta G^\circ+\lambda)^2}{4\lambda k_BT}\big)$.

Model. Donor and acceptor diabatic states with displaced harmonic potentials along a nuclear coordinate of
frequency $\omega_0$ (the [two-parabola model](marcus-two-parabola-model.md) with reorganization energy $\lambda=\hbar\omega_0S_{AD}>0$,
$S_{AD}$ the squared dimensionless displacement) are coupled by a constant electronic matrix element $J_{AD}$
(Condon approximation), weak enough for Fermi's golden rule. Tokmakoff evaluates the golden-rule rate in the
classical limit $\hbar\omega_0\ll k_BT$, neglects the imaginary part of the lineshape function, and replaces
$1-\cos\omega_0t$ by its short-time form $\omega_0^2t^2/2$, a Gaussian approximation of the time integral that is
appropriate when the nuclear modes form a dense, effectively continuous bath (it is not exact for a single
undamped oscillator, whose correlation function is periodic). With the average energy gap identified with the
standard reaction free energy, the resulting **nonadiabatic Marcus rate** is

$$w_{\mathrm{ET}}=\frac{|J_{AD}|^2}{\hbar}\sqrt{\frac{\pi}{\lambda k_BT}}\;\exp\!\Big(-\frac{(\Delta G^\circ+\lambda)^2}{4\lambda k_BT}\Big),$$

that is, the Marcus rate with prefactor $A=\frac{|J_{AD}|^2}{\hbar}\sqrt{\pi/(\lambda k_BT)}$. For a fixed donor–acceptor pair
$J_{AD}$ is a parameter; across pairs its distance dependence is often modelled as $J_{AD}\propto e^{-\beta_ER_{AD}}$. With
an added high-frequency intramolecular mode the rate becomes a Huang–Rhys-weighted sum of such terms.

## Context

Graduate chemical physics. This is the form used to estimate hopping rates between redox sites, for example in theories of charge transport through redox-active molecular solids; the quantum-chemistry inputs are $J_{AD}$ and $\lambda$.

## Depends on

- [Marcus two-parabola model and the reorganization energy](marcus-two-parabola-model.md)

## Proof depends on

None.

## Expansion

A model definition, with its derivation recorded as motivation: the golden-rule rate with the displaced-oscillator correlation function (Tokmakoff Eqs. 19.4.13–19.4.24), the classical, real-part and short-time approximations (Eq. 19.4.27), and the Gaussian time integral giving Eq. 19.4.28.

## Sources

- A. Tokmakoff, *Time-Dependent Quantum Mechanics and Spectroscopy*, Chemistry LibreTexts edition, Section 19.4 (Marcus Theory for Electron Transfer), Eqs. 19.4.12, 19.4.26–19.4.30. [Section 19.4](https://chem.libretexts.org/Bookshelves/Physical_and_Theoretical_Chemistry_Textbook_Maps/Time-Dependent_Quantum_Mechanics_and_Spectroscopy_2025e_%28Tokmakoff%29/19%3A_Energy_and_Charge_Transfer/19.04%3A_Marcus_Theory_for_Electron_Transfer)

# Gouy–Chapman differential capacitance

For a symmetric $z{:}z$ electrolyte the nonlinear Poisson–Boltzmann double layer has scaled diffuse charge $\tilde q=-2\sinh(\tilde\psi_D/2)$ and differential capacitance $C_D=(\varepsilon/\lambda_D)\cosh(ze\psi_D/2k_BT)$, which grows with $|\psi_D|$.

Model (Gouy–Chapman). A planar surface at $x=0$ contacts a dilute symmetric $z{:}z$ electrolyte ($z\ge1$) of bulk
ion number concentration $c_0>0$ per species, permittivity $\varepsilon>0$ and temperature $T>0$, and the excess
potential $\psi$ obeys

$$-\varepsilon\frac{d^2\psi}{dx^2}=zec_0\big(e^{-ze\psi/k_BT}-e^{ze\psi/k_BT}\big),\qquad \psi(0)=\psi_D,\quad \psi(x)\to0\ (x\to\infty).$$

With $\tilde\psi(\tilde x)=ze\psi(\lambda_D\tilde x)/k_BT$ and $\lambda_D=\sqrt{\varepsilon k_BT/(2z^2e^2c_0)}$ this is the reduced equation
$\tilde\psi''=\sinh\tilde\psi$ with decay, i.e. a [decaying Poisson–Boltzmann solution](../../../Biology/not-yet-classified/gouy-chapman/is-decaying-pbsolution.md).
For the decaying solution with $\tilde\psi(0)=\tilde\psi_D$, the scaled diffuse charge
$\tilde q=q/(\varepsilon k_BT/(ze\lambda_D))$, with $q=\int_0^\infty\rho\,dx$, is

$$\tilde q=-2\sinh(\tilde\psi_D/2),$$

and the differential capacitance per unit area is

$$C_D=-\frac{dq}{d\psi_D}=\frac{\varepsilon}{\lambda_D}\cosh\!\Big(\frac{ze\psi_D}{2k_BT}\Big)\ \ge\ \frac{\varepsilon}{\lambda_D},$$

with equality only at $\psi_D=0$, where it reduces to the [Debye–Hückel capacitance](debye-hueckel-double-layer-capacitance.md);
$C_D$ increases with $|\psi_D|$.

## Context

Graduate electrochemistry. The unbounded growth of $C_D$ with voltage is an artefact of point ions; crowding and a compact (Stern) layer limit it in real electrodes, including double-layer capacitors built from conductive metal–organic frameworks.

## Depends on

- [Is Decaying PBSolution](../../../Biology/not-yet-classified/gouy-chapman/is-decaying-pbsolution.md)
- [Debye–Hückel capacitance of a diffuse double layer](debye-hueckel-double-layer-capacitance.md)

## Proof depends on

- [Prescribed surface potential](../../../Biology/not-yet-classified/gouy-chapman/exists-unique-potential.md)
- [Gc Profile](../../../Biology/not-yet-classified/gouy-chapman/gc-profile.md)
- [The potential–`g`–charge bridge](../../../Biology/not-yet-classified/gouy-chapman/potential-g-charge-bridge.md)
- [Reduction to the dimensionless equation](../../../Biology/not-yet-classified/gouy-chapman/reduced-equation-iff-debye.md)

## Expansion

Proof idea (Lecture 25, Eqs. (7)–(8)): multiply $\tilde\psi''=\sinh\tilde\psi$ by $\tilde\psi'$ and integrate to infinity using $\tilde\psi,\tilde\psi'\to0$, so $(\tilde\psi')^2=4\sinh^2(\tilde\psi/2)$ and, for the decaying branch, $\tilde\psi'=-2\sinh(\tilde\psi/2)$; then $q=-\varepsilon\int\psi''dx=\varepsilon\psi'(0)$ gives $\tilde q$, and differentiation gives $C_D$. The proof uses the explicit Gouy–Chapman profile (a definition) and its derivative, the prescribed-surface-potential uniqueness with $g=\tanh(\tilde\psi_D/4)$, the potential–$g$–charge bridge giving $4g/(1-g^2)=2\sinh(\tilde\psi_D/2)$, and the scaling lemma applied with charge $ze$ in place of $e$. A good expansion proves those three results and records the flux identity $q=\varepsilon\psi'(0)$ (from $\psi'(x)\to0$) as its own step.

## Sources

- M. Z. Bazant, *10.626 Electrochemical Energy Systems*, MIT OpenCourseWare, Spring 2014, lecture notes, Lecture 25: Diffuse double layer structure, Sec. 2, Eqs. (7)–(8). [Lecture PDF](https://old.ocw.mit.edu/courses/chemical-engineering/10-626-electrochemical-energy-systems-spring-2014/lecture-notes/MIT10_626S14_S11lec25.pdf); [course](https://ocw.mit.edu/courses/10-626-electrochemical-energy-systems-spring-2014/)

# Debye–Hückel capacitance of a diffuse double layer

In the linearized model, the potential next to a planar electrode decays as $\psi_De^{-x/\lambda_D}$ and the diffuse layer has differential capacitance $C_D=\varepsilon/\lambda_D$ per unit area: a parallel-plate capacitor of width $\lambda_D$.

Model. A planar surface at $x=0$ is in contact with a dilute electrolyte ($x\ge0$) of permittivity
$\varepsilon>0$ at temperature $T>0$, with ion species $i$ of charge numbers $z_i$ and bulk number concentrations
$\nu_ic_0\ge0$, bulk-electroneutral, and with

$$\lambda_D=\sqrt{\frac{\varepsilon k_BT}{\sum_i(z_ie)^2\nu_ic_0}}>0\qquad\text{where }\sum_iz_i^2\nu_ic_0>0 .$$

In the linearized (Debye–Hückel) model of the diffuse layer the excess potential $\psi$ satisfies
$\psi''=\psi/\lambda_D^2$ on $[0,\infty)$, the charge density is $\rho=-\varepsilon\psi''$, and $\psi$ is bounded. Then for
$\psi(0)=\psi_D$:

$$\psi(x)=\psi_De^{-x/\lambda_D},\qquad q=\int_0^\infty\rho\,dx=-\frac{\varepsilon\psi_D}{\lambda_D},\qquad C_D=-\frac{dq}{d\psi_D}=\frac{\varepsilon}{\lambda_D}.$$

Here $q$ is the diffuse charge per unit area (the surface carries $-q$). The linearization is valid for
$|z_ie\psi_D|\ll k_BT$; the exponential and the constant capacitance are exact only in the linearized model.

## Context

Graduate electrochemistry. Electric double-layer capacitors, including the conductive metal–organic framework electrodes studied by Dincă's group and others, store charge in such layers; this linear model is the small-voltage limit of the Gouy–Chapman model.

## Depends on

None.

## Proof depends on

- [A bounded steady state on the half-line decays as e^(−x/λ)](../../../Biology/mathematical-neuroscience/nernst-potential-and-the-steady-state-cable-equa/eq-exp-of-bounded.md)

## Expansion

With $V=\psi$ and $I=-\psi'$, $(V,I)$ is a [steady state of the passive cable](../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/is-steady-state.md) with $r_i=1$, $r_m=\lambda_D^2$; the half-line lemma gives $\psi=\psi_De^{-x/\lambda_D}$ for bounded $\psi$. Then $\rho=-\varepsilon\psi/\lambda_D^2$ integrates to $q=-\varepsilon\psi_D/\lambda_D$, and differentiating in $\psi_D$ gives $C_D$ (Lecture 25, Eqs. (5)–(6)).

## Sources

- M. Z. Bazant, *10.626 Electrochemical Energy Systems*, MIT OpenCourseWare, Spring 2014, lecture notes, Lecture 25: Diffuse double layer structure, Sec. 1 and Sec. 1.1, Eqs. (5)–(6). [Lecture PDF](https://old.ocw.mit.edu/courses/chemical-engineering/10-626-electrochemical-energy-systems-spring-2014/lecture-notes/MIT10_626S14_S11lec25.pdf); [course](https://ocw.mit.edu/courses/10-626-electrochemical-energy-systems-spring-2014/)

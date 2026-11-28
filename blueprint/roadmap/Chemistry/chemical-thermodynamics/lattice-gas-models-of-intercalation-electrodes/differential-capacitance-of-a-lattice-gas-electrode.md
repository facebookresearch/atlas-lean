# Differential capacitance of an ideal lattice-gas electrode

The quasi-static differential (pseudo)capacitance of an ideal lattice-gas intercalation electrode with $N_s$ sites is $C(V)=\frac{e^2N_s}{k_BT}x(1-x)=\frac{e^2N_s}{4k_BT}\operatorname{sech}^2\frac{e(V-V_0)}{2k_BT}$, a single symmetric peak of height $e^2N_s/(4k_BT)$ at $V=V_0$.

For the [ideal lattice-gas electrode](open-circuit-voltage-of-a-lattice-gas-electrode.md) with $N_s>0$ sites, let
$Q(V)=eN_s\,x(V)$ be the charge of the intercalated ions at equilibrium voltage $V$, and define the differential
capacitance $C(V)=-dQ/dV$ (insertion proceeds as $V$ decreases). Then

$$C(V)=\frac{e^2N_s}{k_BT}\,x(1-x)=\frac{e^2N_s}{4k_BT}\operatorname{sech}^2\!\Big(\frac{e(V-V_0)}{2k_BT}\Big)>0 .$$

$C$ is even in $V-V_0$, has its unique maximum $e^2N_s/(4k_BT)$ at $V=V_0$, decays as $e^{-e|V-V_0|/k_BT}$, and
$\int_{-\infty}^{\infty}C(V)\,dV=eN_s$, the total Faradaic capacity of the model. If the electrode stays at equilibrium
during a linear sweep $V(t)$ with signed scan rate $S=dV/dt$ (quasi-static limit), the insertion current is
$dQ/dt=-C(V)\,S$; its magnitude $C(V)|S|$ traces a peak whose height is proportional to $|S|$.

## Context

Graduate electrochemistry. This Faradaic pseudocapacitance is how intercalation in layered, electrically conductive hosts can look capacitive in cyclic voltammetry; the peak width set by $k_BT/e$ is the fingerprint of a single ideal redox site population.

## Depends on

- [Open-circuit voltage of an ideal lattice-gas electrode](open-circuit-voltage-of-a-lattice-gas-electrode.md)

## Proof depends on

None.

## Expansion

Differentiate $x(V)=\frac12(1-\tanh u)$, $u=e(V-V_0)/2k_BT$: $-dx/dV=\frac{e}{4k_BT}\operatorname{sech}^2u=\frac{e}{k_BT}x(1-x)$. The integral is $eN_s[x(-\infty)-x(\infty)]=eN_s$. The sweep statement is the chain rule $dQ/dt=(dQ/dV)(dV/dt)$ (2014 Lecture 14; Lecture 37, Sec. 1).

## Sources

- M. Z. Bazant, *10.626 Electrochemical Energy Systems*, MIT OpenCourseWare, Spring 2014, lecture notes, Lecture 14 (2014): Linear Sweep Voltammetry, charge equation and pseudocapacitance with $\operatorname{sech}^2$; peak at $V_0$ growing linearly with scan rate. [Lecture PDF](https://ocw.mit.edu/courses/10-626-electrochemical-energy-systems-spring-2014/984202229edbf449848905003e62262a_MIT10_626_S14_Lec14_HW6.pdf); [course](https://ocw.mit.edu/courses/10-626-electrochemical-energy-systems-spring-2014/)
- M. Z. Bazant, *10.626 Electrochemical Energy Systems*, MIT OpenCourseWare, Spring 2014, lecture notes, Lecture 37: Pseudocapacitors and batteries, Sec. 1 (differential pseudocapacitance of the lattice-gas model). [Lecture PDF](https://old.ocw.mit.edu/courses/chemical-engineering/10-626-electrochemical-energy-systems-spring-2014/lecture-notes/MIT10_626S14_S11lec37.pdf); [course](https://ocw.mit.edu/courses/10-626-electrochemical-energy-systems-spring-2014/)

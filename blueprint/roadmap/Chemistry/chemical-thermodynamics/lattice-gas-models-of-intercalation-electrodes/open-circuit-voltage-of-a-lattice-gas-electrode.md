# Open-circuit voltage of an ideal lattice-gas electrode

For an ideal lattice-gas intercalation electrode the equilibrium voltage $V(x)=V_0-\frac{k_BT}{e}\ln\frac{x}{1-x}$ is a strictly decreasing bijection from $(0,1)$ onto $\mathbb R$, with inverse $x(V)=\tfrac12\big(1-\tanh\frac{e(V-V_0)}{2k_BT}\big)$.

Let the electrode's equilibrium (Nernst) voltage be $V(x)=V_0-\mu(x)/e$, with $\mu$ the chemical potential of the
[regular-solution model](regular-solution-model-of-an-intercalation-host.md) for $\Omega=0$ and $V_0$ the voltage at half filling (activities of the
other reactants held fixed). Then

$$V(x)=V_0-\frac{k_BT}{e}\ln\frac{x}{1-x}\qquad(0<x<1)$$

is a smooth strictly decreasing bijection $(0,1)\to\mathbb R$ with $V(\tfrac12)=V_0$, and its inverse is the Fermi
function

$$x(V)=\frac{1}{1+e^{e(V-V_0)/k_BT}}=\frac12\Big(1-\tanh\frac{e(V-V_0)}{2k_BT}\Big).$$

$V$ is antisymmetric about half filling: $V(1-x)-V_0=-(V(x)-V_0)$.

## Context

Graduate electrochemistry. It explains the sloping, S-shaped discharge curves of solid-solution intercalation electrodes; for $\Omega>2k_BT$ the homogeneous model instead loses monotonicity and the equilibrium voltage of the phase-separated electrode is flat.

## Depends on

- [Regular-solution model of an intercalation host](regular-solution-model-of-an-intercalation-host.md)

## Proof depends on

- [Mean value theorem for real functions](../../../Analysis/real-functions/differential-calculus/mean-value-theorem.md)
- [Intermediate value theorem](../../../Analysis/real-functions/continuity-and-functional-equations/intermediate-value-theorem.md)

## Expansion

$V'(x)=-\frac{k_BT}{e}\frac{1}{x(1-x)}<0$, so $V$ is strictly decreasing by the mean value theorem; $V\to+\infty$ as $x\to0^+$ and $V\to-\infty$ as $x\to1^-$, so continuity and the intermediate value theorem give surjectivity. Solving $\ln\frac{x}{1-x}=-e(V-V_0)/k_BT$ gives the Fermi function, and $\frac1{1+e^{2u}}=\frac12(1-\tanh u)$ (2014 Lecture 14, ideal solution model).

## Sources

- M. Z. Bazant, *10.626 Electrochemical Energy Systems*, MIT OpenCourseWare, Spring 2014, lecture notes, Lecture 14 (2014): Linear Sweep Voltammetry, ideal solution / lattice gas model: interfacial voltage and its inversion with $\tanh$. [Lecture PDF](https://ocw.mit.edu/courses/10-626-electrochemical-energy-systems-spring-2014/984202229edbf449848905003e62262a_MIT10_626_S14_Lec14_HW6.pdf); [course](https://ocw.mit.edu/courses/10-626-electrochemical-energy-systems-spring-2014/)
- M. Z. Bazant, *10.626 Electrochemical Energy Systems*, MIT OpenCourseWare, Spring 2014, lecture notes, Lecture 11: Reconstitution electrodes, open-circuit voltage $\bar V_0(x)=\bar V_0-\bar\mu(x)/e$. [Lecture PDF](https://old.ocw.mit.edu/courses/chemical-engineering/10-626-electrochemical-energy-systems-spring-2014/lecture-notes/MIT10_626S14_S11lec11.pdf); [course](https://ocw.mit.edu/courses/10-626-electrochemical-energy-systems-spring-2014/)

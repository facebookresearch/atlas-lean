# Spinodal of the regular solution

In the regular-solution model with $\Omega>0$ the free energy has negative curvature, so a homogeneous state is unstable to spinodal decomposition, exactly where $x(1-x)>k_BT/(2\Omega)$; for $\Omega>2k_BT$ this is the interval between $x_\pm=\tfrac12\big(1\pm\sqrt{1-2k_BT/\Omega}\big)$.

For the [regular-solution model](regular-solution-model-of-an-intercalation-host.md) with $\Omega>0$, $T>0$ and $0<x<1$,

$$g''(x)<0\iff x(1-x)>\frac{k_BT}{2\Omega} .$$

Since $\max_{0<x<1}x(1-x)=\tfrac14$, this set is empty if $\Omega\le2k_BT$ (at $\Omega=2k_BT$ only $x=\tfrac12$ has $g''=0$). If
$\Omega>2k_BT$ it is the open interval $(x_-,x_+)$ with

$$x_\pm=\frac12\Big(1\pm\sqrt{1-\frac{2k_BT}{\Omega}}\Big),$$

the spinodal compositions, at which $g''=0$; in the variable $y=2x-1$ the spinodal is $1-y^2=2k_BT/\Omega$. Near the
endpoints, where $x(1-x)<k_BT/(2\Omega)$, the curvature is positive. On $(x_-,x_+)$ the homogeneous-branch chemical
potential $\mu=g'$ decreases with $x$, so the homogeneous-branch voltage $V_0-\mu/e$ increases with filling there; the
equilibrium voltage of the phase-separated electrode is not given by this branch.

## Context

Graduate electrochemistry. Inside the spinodal an intercalation particle cannot fill uniformly and decomposes spontaneously; between the spinodal and the coexistence (binodal) compositions it is metastable.

## Depends on

- [Regular-solution model of an intercalation host](regular-solution-model-of-an-intercalation-host.md)

## Proof depends on

- [Critical interaction for convexity of the regular solution](critical-interaction-for-phase-separation.md)

## Expansion

From $g''=-2\Omega+k_BT/(x(1-x))$ and $\Omega>0$: $g''<0\iff k_BT/(x(1-x))<2\Omega\iff x(1-x)>k_BT/(2\Omega)$. The quadratic $x^2-x+k_BT/(2\Omega)=0$ has the real roots $x_\pm$ exactly when $1-2k_BT/\Omega\ge0$, and $x(1-x)$ exceeds its value at the roots exactly between them; with $x(1-x)=(1-y^2)/4$ this is Lecture 11, Eq. (8), $\tilde h_0^{-1}=1-y^2$.

## Sources

- M. Z. Bazant, *10.626 Electrochemical Energy Systems*, MIT OpenCourseWare, Spring 2014, lecture notes, Lecture 11: Reconstitution electrodes, Sec. 1.4 (spinodal decomposition where $\bar g''<0$, Eq. (8)). [Lecture PDF](https://old.ocw.mit.edu/courses/chemical-engineering/10-626-electrochemical-energy-systems-spring-2014/lecture-notes/MIT10_626S14_S11lec11.pdf); [course](https://ocw.mit.edu/courses/10-626-electrochemical-energy-systems-spring-2014/)

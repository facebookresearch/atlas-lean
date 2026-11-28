# Critical interaction for convexity of the regular solution

The regular-solution free energy is convex on $[0,1]$, and its chemical potential strictly increasing, exactly when $\Omega\le2k_BT$; for $\Omega>2k_BT$ the homogeneous state near half filling is locally unstable. For $\Omega>0$ the threshold is the critical temperature $T_c=\Omega/(2k_B)$.

For the [regular-solution model](regular-solution-model-of-an-intercalation-host.md) with $T>0$ and $\Omega\in\mathbb R$:

$$g''(x)=-2\Omega+\frac{k_BT}{x(1-x)}\qquad(0<x<1),\qquad \min_{0<x<1}g''(x)=g''(\tfrac12)=4k_BT-2\Omega .$$

Hence the following are equivalent: (i) $\Omega\le2k_BT$; (ii) $g$ is convex on $[0,1]$; (iii) $\mu=g'$ is strictly
increasing on $(0,1)$; (iv) the homogeneous-branch open-circuit voltage $V_0-\mu(x)/e$ is strictly decreasing in $x$.
When they hold, $g$ is strictly convex (at $\Omega=2k_BT$, $g''$ vanishes only at $x=\tfrac12$). If $\Omega>2k_BT$, then
$g''<0$ near $x=\tfrac12$: $g$ is not convex, $\mu$ is not monotone, and a homogeneous filling fraction there is
locally unstable to composition fluctuations. For $\Omega>0$ the condition $\Omega\le2k_BT$ reads $T\ge T_c=\Omega/(2k_B)$.

## Context

Graduate electrochemistry. Below $T_c$, a host whose mean filling lies in the miscibility gap (between the binodal compositions) separates into lean and rich phases with a flat equilibrium voltage, as for Li$_x$FePO$_4$; outside the gap the homogeneous state remains the equilibrium. The binodal compositions come from the common-tangent construction, which is not part of this page.

## Depends on

- [Regular-solution model of an intercalation host](regular-solution-model-of-an-intercalation-host.md)

## Proof depends on

- [Mean value theorem for real functions](../../../Analysis/real-functions/differential-calculus/mean-value-theorem.md)

## Expansion

$x(1-x)\le\tfrac14$ with equality only at $x=\tfrac12$ gives the minimum of $g''$. If $\Omega\le2k_BT$, then $g''\ge0$ with equality at most at $x=\tfrac12$, so $g'$ is strictly increasing on $(0,1)$ by the mean value theorem (a zero of a nonnegative derivative at a single point does not stop strict increase), hence $g$ is strictly convex on $(0,1)$ and, being continuous, on $[0,1]$. If $\Omega>2k_BT$, $g''(\tfrac12)<0$ and by continuity $g''<0$ on a neighbourhood. The critical condition is Lecture 11's $\tilde h_0=h_0/(2k_BT)=1$.

## Sources

- M. Z. Bazant, *10.626 Electrochemical Energy Systems*, MIT OpenCourseWare, Spring 2014, lecture notes, Lecture 11: Reconstitution electrodes, Sec. 1.3 (critical temperature $h_0=2k_BT_c$, dimensionless $\tilde\mu=-\tilde h_0y+\operatorname{artanh}y$) and Sec. 1.4. [Lecture PDF](https://old.ocw.mit.edu/courses/chemical-engineering/10-626-electrochemical-energy-systems-spring-2014/lecture-notes/MIT10_626S14_S11lec11.pdf); [course](https://ocw.mit.edu/courses/10-626-electrochemical-energy-systems-spring-2014/)
- M. Z. Bazant, Theory of chemical kinetics and charge transfer based on nonequilibrium thermodynamics, *Accounts of Chemical Research* 46 (2013), 1144–1160; numbers from arXiv:1208.1587v5, discussion after Eq. (60) (phase separation of the regular solution for $\Omega>2k_BT$). [arXiv:1208.1587v5](https://arxiv.org/abs/1208.1587v5); [doi:10.1021/ar300145c](https://doi.org/10.1021/ar300145c)

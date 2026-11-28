# Regular-solution model of an intercalation host

An intercalation host is modelled as a lattice of sites with filling fraction $x$ and per-site free energy $g(x)=\Omega x(1-x)+k_BT\,[x\ln x+(1-x)\ln(1-x)]$; its chemical potential is $\mu(x)=\Omega(1-2x)+k_BT\ln\frac{x}{1-x}$, and $\Omega=0$ is the ideal lattice gas.

Let intercalated particles (for example $\mathrm{Li}^+$ with an electron, a neutral polaron) occupy a fraction
$x\in[0,1]$ of $N_s$ equivalent host sites at temperature $T>0$, with a mean-field pair-interaction parameter
$\Omega\in\mathbb R$, and consider a homogeneous host (no composition gradients). The **regular-solution model** gives the
free energy per site, after removing a reference term linear in $x$, as

$$g(x)=\Omega\,x(1-x)+k_BT\big[x\ln x+(1-x)\ln(1-x)\big]\qquad(0\ln0=0),$$

whose entropic part is $-T$ times the ideal mixing entropy of particles and vacancies per site (the binary mixing
entropy with the molar $R$ replaced by $k_B$ per site). The convention $0\ln0=0$ extends $g$ to $[0,1]$; $\mu$ below is
defined only on $(0,1)$. On $(0,1)$
the chemical potential of an intercalated particle (relative to its standard value) is

$$\mu(x)=g'(x)=\Omega(1-2x)+k_BT\ln\frac{x}{1-x}=\Omega(1-2x)+2k_BT\operatorname{artanh}(2x-1).$$

For $\Omega=0$ (the **ideal lattice gas** or ideal solid solution) $\mu=k_BT\ln\frac{x}{1-x}$, i.e. activity
$a=x/(1-x)$ and activity coefficient $\gamma=1/(1-x)$ relative to $x$; $\gamma\to\infty$ as $x\to1$ because of
crowding. $\Omega>0$ corresponds to effective attraction between intercalated particles and favours phase
separation.

## Context

Graduate electrochemistry of intercalation electrodes. The model describes the voltage profiles of Li-ion electrode materials, from solid-solution (sloping) to phase-separating (flat) behaviour, and is the thermodynamic starting point for intercalation pseudocapacitance in layered hosts such as conductive coordination polymers and layered organic cathodes.

## Depends on

- [Entropy of mixing of a binary mixture](../entropy-heat-engines-and-the-third-law/entropy-of-mixing-binary.md)

## Proof depends on

None.

## Expansion

A model definition. $\mu=g'$ by direct differentiation, and $\ln\frac{x}{1-x}=2\operatorname{artanh}(2x-1)$. The ideal case comes from counting the $\binom{N_s}{N}$ arrangements with Stirling's formula (Lecture 7); the interaction term is the mean-field enthalpy of mixing (Lecture 11, Eqs. (1)–(3); Bazant, Eqs. (59)–(60)).

## Sources

- M. Z. Bazant, *10.626 Electrochemical Energy Systems*, MIT OpenCourseWare, Spring 2014, lecture notes, Lecture 11: Reconstitution electrodes, Eqs. (1)–(3) (regular solution, $h_0$ written $\Omega$ here). [Lecture PDF](https://old.ocw.mit.edu/courses/chemical-engineering/10-626-electrochemical-energy-systems-spring-2014/lecture-notes/MIT10_626S14_S11lec11.pdf); [course](https://ocw.mit.edu/courses/10-626-electrochemical-energy-systems-spring-2014/)
- M. Z. Bazant, *10.626 Electrochemical Energy Systems*, MIT OpenCourseWare, Spring 2014, lecture notes, Lecture 8: The Nernst Equation, Sec. 1, Eqs. (8)–(9) (lattice gas activity and activity coefficient). [Lecture PDF](https://old.ocw.mit.edu/courses/chemical-engineering/10-626-electrochemical-energy-systems-spring-2014/lecture-notes/MIT10_626S14_S11lec08.pdf); [course](https://ocw.mit.edu/courses/10-626-electrochemical-energy-systems-spring-2014/)
- M. Z. Bazant, Theory of chemical kinetics and charge transfer based on nonequilibrium thermodynamics, *Accounts of Chemical Research* 46 (2013), 1144–1160; numbers from arXiv:1208.1587v5, Eqs. (59)–(60) (regular solution free energy and chemical potential). [arXiv:1208.1587v5](https://arxiv.org/abs/1208.1587v5); [doi:10.1021/ar300145c](https://doi.org/10.1021/ar300145c)

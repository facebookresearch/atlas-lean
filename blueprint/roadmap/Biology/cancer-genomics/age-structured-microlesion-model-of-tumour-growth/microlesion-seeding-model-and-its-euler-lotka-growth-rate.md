# Microlesion seeding model and its Euler–Lotka growth rate

A tumour is a collection of non-interacting microlesions. A lesion of type $n$ (the number of drivers of its founding cell) and age $a$ has deterministic volume $V_n(a)$, a fraction $r_n(a)$ of type-$n$ cells and $1 - r_n(a)$ of type-$(n+1)$ cells, and seeds new lesions at rate $\phi_n(a)$; a new lesion has age $0$ and type $n$ with probability $r_n(a)$ or $n + 1$ with probability $1 - r_n(a)$. The expected number density $f_n(a, t)$ of type-$n$ lesions of age $a$ at time $t$ satisfies

$$\frac{\partial f_n}{\partial t} + \frac{\partial f_n}{\partial a} = 0, \qquad f_n(0, t) = \int_0^\infty \Big(\phi_n(a)\,r_n(a)\,f_n(a,t) + \phi_{n-1}(a)\,\big(1 - r_{n-1}(a)\big)\,f_{n-1}(a,t)\Big)\,da,$$

with $f_0 \equiv 0$ and $f_n(a, 0) = \delta_{n,1}\delta(a)$. The expected total volume is $V_{\mathrm{tot}}(t) = \sum_n\int_0^\infty f_n(a,t)\,V_n(a)\,da$.

**One lesion type.** Without new drivers ($r_1 \equiv 1$) the system is the McKendrick–von Foerster equation without removal, $\partial_t f + \partial_a f = 0$, $f(0,t) = \int_0^\infty \phi(a) f(a,t)\,da$, $f(a,0) = \delta(a)$. Its solution is $f(a,t) = F(t-a)\Theta(t-a) + \delta(t-a)$, where the birth density $F$ has Laplace transform

$$\tilde F(s) = \frac{\tilde\phi(s)}{1 - \tilde\phi(s)}, \qquad \tilde\phi(s) = \int_0^\infty e^{-sa}\phi(a)\,da .$$

Assume the seeding rate $\phi \ge 0$ is locally integrable and not almost everywhere zero, and that the Euler–Lotka equation

$$\int_0^\infty \phi(a)\,e^{-Ga}\,da = 1$$

has a real root $G$; it is unique, because $\tilde\phi$ is strictly decreasing where it is finite. Assume the seeding is supercritical, $G > 0$, which (given the root) is equivalent to $\int_0^\infty \phi(a)\,da > 1$. The tilted kernel $\phi_G(a) = \phi(a)e^{-Ga}$ is a probability density on $[0,\infty)$; assume its mean $m = \int_0^\infty a\,\phi(a)e^{-Ga}\,da$ is finite. Then the number of lesions $N(t) = \int_0^\infty f(a,t)\,da = 1 + \int_0^t F$ satisfies

$$N(t) \sim \frac{e^{Gt}}{G\,m} \qquad (t \to \infty).$$

If moreover $\phi_G$ is continuous almost everywhere and dominated by a nonincreasing integrable function (so that it is directly Riemann integrable), then $F(t) \sim e^{Gt}/m$, i.e. $f(a,t) \sim A\,e^{G(t-a)}$ for each fixed age $a$ with $A = 1/m$. If the lesion volume $V$ is nondecreasing and absolutely continuous with $V(0) = 0$ and $\int_0^\infty V(a)e^{-Ga}\,da < \infty$, then $V_{\mathrm{tot}}(t) \sim \frac{e^{Gt}}{m}\int_0^\infty V(a)e^{-Ga}\,da$. Without supercriticality the conclusion fails: if $\int_0^\infty \phi < 1$, then $N(t)$ stays bounded, converging to $1/(1 - \int_0^\infty \phi)$.

## Depends on

- [The one-sided Laplace transform](../../../Analysis/harmonic-analysis/integral-transforms/laplace-transform/laplace.md)

## Proof depends on

- [Renewal equation for exponential growth](../../epidemiology/euler-lotka-equation-and-the-reproduction-number/renewal-exp-iff.md)
- [Laplace transform of a causal convolution](../../../Analysis/harmonic-analysis/integral-transforms/laplace-transform/laplace-transform-of-a-causal-convolution.md)
- [Nonlattice constant identification](../../../Probability/point-processes/renewal-limits-nonlattice-constants-versus-latti/tendsto-scaled-of-key-renewal.md)

## Proof sketch

The transport equation only ages lesions, so the density along characteristics is the birth rate at time $t - a$, plus the initial lesion travelling along $a = t$. Inserting this form in the boundary condition gives the renewal equation $F(t) = \phi(t) + \int_0^t \phi(a)F(t-a)\,da$, whose Laplace transform is $\tilde F = \tilde\phi + \tilde\phi\tilde F$. Singularities of $\tilde F$ are at the roots of $\tilde\phi(s) = 1$; the rightmost one, $G$, dominates the inverse transform and fixes the exponential growth rate. To make this rigorous, integrate the renewal equation: $N = 1 + \phi * N$, so $e^{-Gt}N(t)$ solves the renewal equation with input $e^{-Gt}$ (nonincreasing and integrable because $G > 0$) for the nonlattice probability density $\phi_G$, and the key renewal theorem gives the limit $\int_0^\infty e^{-Gt}\,dt/m = 1/(Gm)$. The same argument with input $\phi_G$ gives $e^{-Gt}F(t) \to 1/m$, and writing $V_{\mathrm{tot}}(t) = \int_0^t V'(a)\,N(t-a)\,da$ (an integration by parts using $V(0) = 0$) and dominated convergence gives the volume asymptotics. The hierarchical structure (type $n$ is fed only by types $n$ and $n-1$) lets the multi-driver system be solved type by type in the same way (Methods of the source).

## Sources

- C. Paterson, M. A. Nowak, B. Waclaw, "An exactly solvable, spatial model of mutation accumulation in cancer", Scientific Reports (2016), <https://doi.org/10.1038/srep39511> (PMC5177951).

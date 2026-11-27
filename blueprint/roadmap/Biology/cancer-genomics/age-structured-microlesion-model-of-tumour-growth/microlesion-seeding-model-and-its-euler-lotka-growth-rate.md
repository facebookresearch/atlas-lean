# Microlesion seeding model and its Euler–Lotka growth rate

A tumour is a collection of non-interacting microlesions. A lesion of type $n$ (the number of drivers of its founding cell) and age $a$ has deterministic volume $V_n(a)$, a fraction $r_n(a)$ of type-$n$ cells and $1 - r_n(a)$ of type-$(n+1)$ cells, and seeds new lesions at rate $\phi_n(a)$; a new lesion has age $0$ and type $n$ with probability $r_n(a)$ or $n + 1$ with probability $1 - r_n(a)$. The expected number density $f_n(a, t)$ of type-$n$ lesions of age $a$ at time $t$ satisfies

$$\frac{\partial f_n}{\partial t} + \frac{\partial f_n}{\partial a} = 0, \qquad f_n(0, t) = \int_0^\infty \Big(\phi_n(a)\,r_n(a)\,f_n(a,t) + \phi_{n-1}(a)\,\big(1 - r_{n-1}(a)\big)\,f_{n-1}(a,t)\Big)\,da,$$

with $f_0 \equiv 0$ and $f_n(a, 0) = \delta_{n,1}\delta(a)$. The expected total volume is $V_{\mathrm{tot}}(t) = \sum_n\int_0^\infty f_n(a,t)\,V_n(a)\,da$.

**One lesion type.** Without new drivers ($r_1 \equiv 1$) the system is the McKendrick–von Foerster equation without removal, $\partial_t f + \partial_a f = 0$, $f(0,t) = \int_0^\infty \phi(a) f(a,t)\,da$, $f(a,0) = \delta(a)$. Its solution is $f(a,t) = F(t-a)\Theta(t-a) + \delta(t-a)$, where the birth density $F$ has Laplace transform

$$\tilde F(s) = \frac{\tilde\phi(s)}{1 - \tilde\phi(s)}, \qquad \tilde\phi(s) = \int_0^\infty e^{-sa}\phi(a)\,da .$$

If $G$ is the largest real root of the Euler–Lotka equation

$$\int_0^\infty \phi(a)\,e^{-Ga}\,da = 1,$$

then $f(a,t) \sim A\,e^{G(t-a)}$ for large $t$ and some $A > 0$, the number of lesions $N(t) = \int_0^\infty f(a,t)\,da$ grows like $e^{Gt}$, and so does $V_{\mathrm{tot}}(t)$ whenever $\int_0^\infty V(a)e^{-Ga}\,da < \infty$.

## Depends on

- [The one-sided Laplace transform](../../../Analysis/harmonic-analysis/integral-transforms/laplace-transform/laplace.md)

## Proof depends on

- [Renewal equation for exponential growth](../../epidemiology/euler-lotka-equation-and-the-reproduction-number/renewal-exp-iff.md)
- [Laplace transform of a causal convolution](../../../Analysis/harmonic-analysis/integral-transforms/laplace-transform/laplace-transform-of-a-causal-convolution.md)

## Proof sketch

The transport equation only ages lesions, so the density along characteristics is the birth rate at time $t - a$, plus the initial lesion travelling along $a = t$. Inserting this form in the boundary condition gives the renewal equation $F(t) = \phi(t) + \int_0^t \phi(a)F(t-a)\,da$, whose Laplace transform is $\tilde F = \tilde\phi + \tilde\phi\tilde F$. Singularities of $\tilde F$ are at the roots of $\tilde\phi(s) = 1$; the rightmost one, $G$, dominates the inverse transform and fixes the exponential growth rate. The hierarchical structure (type $n$ is fed only by types $n$ and $n-1$) lets the multi-driver system be solved type by type in the same way (Methods of the source).

## Sources

- C. Paterson, M. A. Nowak, B. Waclaw, "An exactly solvable, spatial model of mutation accumulation in cancer", Scientific Reports (2016), <https://doi.org/10.1038/srep39511> (PMC5177951).

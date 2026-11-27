# Decorated age-of-infection model and compartment counts

Let $n(t,a)$ be the density at time $t$ of individuals infected at time $t-a$, so $a \ge 0$ is the age of infection, and let $\tau \ge 0$ with $\int_0^\infty \tau(a)\,da < \infty$ be the mean rate at which an individual of age $a$ causes new infections. The Kermack–McKendrick age-of-infection model is

$$\partial_t n + \partial_a n = 0, \qquad n(t,0) = S(t)\int_0^\infty n(t,a)\,\tau(a)\,da, \qquad n(0,a) = x_0\,g(a), \qquad S(t) = 1 - \int_0^\infty n(t,a)\,da,$$

with $0 \le x_0 \le 1$ and a probability density $g$. Here $n$ counts every individual ever infected, not only infectious ones, so the PDE has no recovery term.

Let $(X(a))_{a\ge 0}$ be a life-cycle process on a finite set of compartments $\mathcal{S}$, describing the compartment of a typical individual at age of infection $a$, and put $p(a,i) = \mathbb{P}(X(a) = i)$. The decorated compartment sizes are

$$n_i(t) = \int_0^\infty n(t,a)\,p(a,i)\,da, \qquad i \in \mathcal{S}.$$

**SIR as a special case.** If $X$ starts in $I$ and jumps to $R$ at rate $\gamma > 0$, and an individual infects at constant rate $\beta$ while in $I$, then $\tau(a) = \beta e^{-\gamma a}$. In that case $I(t) = \int_0^\infty n(t,a)e^{-\gamma a}\,da$ and $R(t) = \int_0^\infty n(t,a)(1-e^{-\gamma a})\,da$ solve

$$\dot S = -\beta IS, \qquad \dot I = \beta IS - \gamma I, \qquad \dot R = \gamma I .$$

## Depends on

- [Solution of the Kermack–McKendrick SIR system](../kermack-mckendrick-sir-model/is-solution.md)

## Expansion

Differentiate $I(t)$ under the integral, use $\partial_t n = -\partial_a n$, and integrate by parts in $a$. This gives $\dot I = n(t,0) - \gamma I$ (assuming $n(t,a)e^{-\gamma a} \to 0$ as $a \to \infty$). The boundary condition with $\tau(a) = \beta e^{-\gamma a}$ gives $n(t,0) = \beta S I$. The same computation gives $\dot R = \gamma I$, and $\dot S = -n(t,0)$ because $\int n\,da$ grows by the inflow at age $0$. The construction works for any life-cycle process $X$, Markov or not, so non-exponential stage durations need no extra compartments: the age profile follows a single one-dimensional PDE, and compartment counts are linear functionals of it.

## Sources

- F. Foutel-Rodier, F. Blanquart, P. Courau, P. Czuppon, J.-J. Duchamps, J. Gamblin, É. Kerdoncuff, R. Kulathinal, L. Régnier, L. Vuduc, A. Lambert, E. Schertzer, *From individual-based epidemic models to McKendrick–von Foerster PDEs: a guide to modeling and inferring COVID-19 dynamics*, Journal of Mathematical Biology 85 (2022), 43, <https://doi.org/10.1007/s00285-022-01794-4>, PMCID PMC9517997. Section 1.2, Eqs. (1)–(3).
- W. O. Kermack, A. G. McKendrick, *A contribution to the mathematical theory of epidemics*, Proceedings of the Royal Society A 115 (1927), 700–721, <https://doi.org/10.1098/rspa.1927.0118>.

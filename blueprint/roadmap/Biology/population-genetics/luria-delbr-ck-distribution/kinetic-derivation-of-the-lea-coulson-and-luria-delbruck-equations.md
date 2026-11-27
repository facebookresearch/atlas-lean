# Kinetic derivation of the Lea–Coulson and Luria–Delbrück equations

**Kinetic model.** Let $f(v,t)$ be the distribution of the number $v$ of mutant cells, with $f(v,0) = \delta_0(v)$. In an elementary interaction the mutant count changes as

$$v^* = v + L(v) + \eta(t),$$

where $L(v) \ge 0$ is the growth of the existing mutant clone and $\eta(t)$ is a Poisson number of new mutations with intensity $\nu(t) = \mu e^{\beta_1 t}$ ($\beta_1$: growth rate of normal cells, $\mu$: mutation rate). In weak form,

$$\frac{d}{dt}\int f(v,t)\varphi(v)\,dv = \Big\langle\int\big(\varphi(v^*) - \varphi(v)\big)f(v,t)\,dv\Big\rangle,$$

and with $\hat f(\xi,t) = \int e^{-i\xi v}f(v,t)\,dv$ and $\widehat M(\xi,t) = \exp\{\mu e^{\beta_1 t}(e^{-i\xi} - 1)\}$,

$$\partial_t\hat f(\xi,t) = \widehat M(\xi,t)\int\langle e^{-i\xi L(v)}\rangle e^{-i\xi v}f(v,t)\,dv - \hat f(\xi,t).$$

Deterministic growth $L(v) = \beta_2 v$ corresponds to the original Luria–Delbrück formulation, and Poisson growth $L(v) \sim \mathrm{Poisson}(\beta_2 v)$ to the Lea–Coulson formulation.

**Theorem (quasi-invariant limit).** Replace $\beta_1, \beta_2, \mu$ by $\varepsilon\beta_1, \varepsilon\beta_2, \varepsilon\mu$ and rescale time as $\tau = \varepsilon t$. As $\varepsilon \to 0$, the weak solution $g_\varepsilon(v,\tau) = f(v,t)$ of the Lea–Coulson kinetic equation converges to a probability density $g(v,\tau)$ whose Fourier transform $G$ solves

$$\partial_\tau G(\xi,\tau) = (e^{-i\xi} - 1)\Big(i\beta_2\,\partial_\xi G(\xi,\tau) + \mu e^{\beta_1\tau}G(\xi,\tau)\Big),$$

the evolution equation for the generating function of the Luria–Delbrück distribution in the Lea–Coulson formulation. For deterministic clone growth the same limit gives

$$\partial_\tau G(\xi,\tau) = \beta_2\xi\,\partial_\xi G(\xi,\tau) + \mu e^{\beta_1\tau}(e^{-i\xi} - 1)G(\xi,\tau),$$

the original Luria–Delbrück formulation. In both cases the mean number of mutants grows identically, so the two formulations differ only in fluctuations.

## Depends on

- [Luria–Delbrück distribution](ld-pmf.md)

## Expansion

The scaling is the grazing (quasi-invariant) limit of kinetic theory: interactions become frequent but each changes the state only slightly. Expanding $\exp\{\varepsilon(\beta_2 v + \mu e^{\beta_1\tau})(e^{-i\xi} - 1)\}$ to first order leaves the drift-plus-jump generator above, with a remainder bounded by $\tfrac12|e^{-i\xi} - 1|^2$ times second moments of $g_\varepsilon$, which stay bounded on finite time intervals; convergence is measured in a Fourier-based metric. The same kinetic framework extends to the fully stochastic Bartlett formulation, in which both normal and mutant counts are random.

## Sources

- Lorenzo Pareschi and Giuseppe Toscani, "The Kinetic Theory of Mutation Rates", *Axioms* 12 (2023), 265, <https://doi.org/10.3390/axioms12030265>. Numbering as in the preprint arXiv:2212.00146v1, <https://arxiv.org/abs/2212.00146v1>: Sections 3–4 (kinetic model, Fourier-transformed equations and Theorem 1).

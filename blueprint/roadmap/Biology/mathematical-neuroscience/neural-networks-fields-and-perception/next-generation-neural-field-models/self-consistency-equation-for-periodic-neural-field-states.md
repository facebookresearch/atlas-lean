# Self-consistency equation for periodic neural-field states

Rescale time so that a $T$-periodic solution of the theta-neuron Ott–Antonsen field has period $2\pi$, with frequency $\omega = 2\pi/T$. Let $\mathcal{U}(W, \zeta, \omega)(x,t)$ denote the unique stable $2\pi$-periodic solution, lying in the open unit disc, of the pointwise complex Riccati equation driven by a real periodic field $W(x, \cdot)$, where $\zeta = (\eta_0 + i\gamma)/(2\omega)$.

A pair $(u, \omega)$ is a $2\pi$-periodic solution built from these stable branches iff $u = \mathcal{U}(W, \zeta, \omega)$, where $(W, \omega)$ solves the **self-consistency equation**

$$
W(x,t) = \frac{\kappa}{2\omega}\, \Big(K * H_n\big(\mathcal{U}(W, \tfrac{\eta_0 + i\gamma}{2\omega}, \omega)\big)\Big)(x,t),
$$

together with a phase-pinning condition such as $\int_0^{2\pi}\!\int_0^{2\pi} W(x,t)\sin(2t)\,dt\,dx = 0$.

**Proposition 1.** If $(W, \omega)$ solves the self-consistency equation and $U = \mathcal{U}(W, \zeta, \omega)$, then for every $x$

$$
\left| \exp\!\int_0^{2\pi} M(x,t)\,dt \right| < 1,
\qquad
M(x,t) = \frac{i}{\omega}\Big[\big(\kappa (K * H_n(U)) + \eta_0 + i\gamma\big)(1 + U) + 1 - U\Big].
$$

That is, the local Floquet multiplier of each pointwise Riccati orbit lies in $\mathbb{D}$. This controls the essential spectrum of the monodromy operator of the periodic neural-field solution.

## Depends on

- [Periodic complex Riccati equation and its Möbius Poincaré map](periodic-complex-riccati-equation-and-its-mobius-poincare-map.md)

## Expansion

Inserting the solution operator into the definition of $W$ eliminates $u$. The unknown becomes the synaptic input field $W$, which is proportional to the current received at $x$, plus the frequency. For the cosine kernel $K = (1 + A\cos x)/(2\pi)$, after removing translation invariance $W$ lies in $\operatorname{span}\{1, \sin x\}$ in space. A Fourier–Galerkin expansion in time then reduces the problem to $4F + 3$ real equations, which Newton's method solves in a few iterations. The cost is linear in the number of spatial grid points, versus quadratic for direct continuation of the discretized field. Proposition 1 follows because the linearization of the Riccati equation about $U$ is $\dot v = (c_1 + 2c_2 U) v$, and $c_1 + 2c_2 U$ equals $M$ after substituting $W$ and $\zeta$. The same construction extends to delays, two-population fields and Winfree oscillators.

## Sources

- Laing CR, Omel'chenko OE. Periodic solutions in next generation neural field models. *Biological Cybernetics* 117 (2023) 259–274. <https://doi.org/10.1007/s00422-023-00969-6>. PMCID: PMC10600056.

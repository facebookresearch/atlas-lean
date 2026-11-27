# Starvation-driven diffusion yields the ideal free distribution and raises the predator invasion threshold

**Starvation-driven diffusion (SDD).** On a bounded domain $\Omega$ with resource $m(x) > 0$ and no-flux boundary, a species of density $u$ moves with motility depending on the starvation measure $s = u/m$ (food demand over supply):

$$u_t = \Delta\big(\gamma_\varepsilon(s)u\big) + u\,(m(x) - u), \qquad \nabla(\gamma_\varepsilon(s)u)\cdot\vec n = 0 \text{ on } \partial\Omega,$$

where $\gamma_\varepsilon$ is a smooth approximation (mollified piecewise-linear interpolation on $[1-\varepsilon, 1+\varepsilon]$) of the step function $\gamma_0(s) = \ell$ for $s < 1$, $\gamma_0(s) = h$ for $s > 1$, with $0 < \ell < h$: individuals move slowly where food is abundant and fast where it is scarce. For small $\varepsilon$ there is a unique positive steady state $\theta_\gamma$, which is globally asymptotically stable.

**Theorem (ideal free distribution).** If

$$\ell\max_{\bar\Omega}m < \frac{h+\ell}{2}\min_{\bar\Omega}m \le \frac{h+\ell}{2}\max_{\bar\Omega}m < h\min_{\bar\Omega}m,$$

then $\theta_\gamma(x) \to m(x)$ as $\varepsilon \to 0$: the population matches the resource distribution exactly. The condition holds when the motility contrast $h/\ell$ is large relative to the spatial variation of $m$.

**Predator–prey model.** With prey $u$, predator $v$,

$$u_t = \Delta(\gamma_{\varepsilon,1}(s_1)u) + u(m - u) - \alpha uv, \qquad v_t = \Delta(\gamma_{\varepsilon,2}(s_2)v) + \beta uv - (c + dv)v,$$

starvation measures $s_1 = u/(m + v)$, $s_2 = (c + v)/u$, and steps $(\ell_i, h_i)$, the only semitrivial state is $(u_0, 0)$ with $u_0$ the prey-only SDD steady state.

**Theorem (predator invasion).** For fixed $\ell_2, h_2$ there is $c^*(\gamma_{\varepsilon,2}) \in (0, \max_{\bar\Omega}u_0)$ such that $(u_0, 0)$ is unstable (the predator invades) if the predator death rate $c < c^*(\gamma_{\varepsilon,2})$ and locally asymptotically stable if $c > c^*(\gamma_{\varepsilon,2})$. Moreover $c^*(\gamma_{\varepsilon,2}) > c^*(\ell_2)$, the threshold for a predator diffusing randomly at constant rate $\ell_2$: starvation-driven dispersal lets the predator persist at higher mortality. If $c \ge \max_{\bar\Omega}u_0$, $(u_0, 0)$ is stable for all $\ell_2, h_2$.

## Proof sketch

At a steady state of SDD, $\gamma(s)u$ solves an elliptic problem; where $s < 1 - \varepsilon$ the flux potential is $\ell u$ and where $s > 1 + \varepsilon$ it is $hu$, and the stated inequalities rule out both regions, forcing $s \to 1$, i.e. $u \to m$, the ideal free distribution with zero net flux and zero local growth. Predator invasion is governed by the principal eigenvalue of the linearisation $\Delta(\gamma_{\varepsilon,2}(c/u_0)\phi) + (\beta u_0 - c)\phi$; because the motility is lowest where prey is abundant ($c/u_0 < 1$), predators linger where their growth rate is positive, increasing the eigenvalue compared with constant diffusion. These analytic predictions are reproduced by multi-agent deep reinforcement learning agents that learn dispersal policies on a grid.

## Sources

- Wonhyung Choi and Inkyung Ahn, "Evolutionary dispersal of ecological species via Multi-Agent Deep Reinforcement Learning", *Ecological Complexity* 64 (2025), 101146, <https://doi.org/10.1016/j.ecocom.2025.101146>. Preprint version: arXiv:2410.18621 (2024), Section 5 (mathematical models with starvation-driven diffusion: single-species ideal free distribution theorem and predator–prey invasion theorems), <https://doi.org/10.48550/arXiv.2410.18621>.

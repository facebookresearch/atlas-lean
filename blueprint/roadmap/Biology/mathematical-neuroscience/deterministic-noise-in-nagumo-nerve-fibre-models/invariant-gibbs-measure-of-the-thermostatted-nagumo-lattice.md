# Invariant Gibbs measure of the thermostatted Nagumo lattice

**Setting.** A nerve fibre is modelled by a finite chain of diffusively coupled Nagumo cells, $\dot u_i=l\,\Delta u_i+f(u_i)$, $i\in I$, with discrete Laplacian $\Delta u_i=u_{i+1}-2u_i+u_{i-1}$ (Neumann ends), coupling $l>0$ and bistable current $f(u)=-ku(u-\alpha)(u-1)$, $0<\alpha<1$, $k>0$. With $V'=-f$, $V(0)=0$, and the energy

$$\mathcal V[u]=\sum_i\Big[\tfrac12l\,(u_i-u_{i-1})^2+V(u_i)\Big],$$

the chain is the gradient flow $\dot u_i=-\partial_i\mathcal V[u]$. Additive Langevin noise of intensity $D$ would give the Gibbs density $\propto e^{-\mathcal V/D}$. Instead, noise is modelled deterministically as fluctuation of membrane characteristics, through a conductance-like multiplier $\lambda$ and local current fluctuations $\eta_i$:

$$\dot u_i=-\lambda\,\partial_i\mathcal V[u]+\eta_i,\qquad \dot\lambda=\frac1{Q_\lambda}\sum_i\Big[(\partial_i\mathcal V[u])^2-D\,\partial_i^2\mathcal V[u]\Big],\qquad \dot\eta_i=-\frac1{Q_\eta}\,\partial_i\mathcal V[u],$$

with parameters $Q_\lambda,Q_\eta>0$.

**Theorem.** For $Q_\lambda,Q_\eta>0$ the augmented measure

$$d\mu\ \propto\ \exp\Big\{-\frac1D\Big(\mathcal V[u]+\tfrac12Q_\lambda\lambda^2+\tfrac12Q_\eta\sum_i\eta_i^2\Big)\Big\}\prod_i du_i\,d\lambda\,d\eta_i$$

is invariant for this extended dynamics, and remains invariant when the extended dynamics is additionally perturbed stochastically in the way specified by the source. Its $u$-marginal is the Langevin equilibrium $\propto e^{-\mathcal V[u]/D}\prod_idu_i$, so the noise intensity $D$ enters only through the feedback rate of the membrane fluctuations. Moreover, if $\lambda$ stays bounded and the time average of $\sum_i\eta_i\partial_i\mathcal V$ vanishes, then the time average of $\lambda\sum_i\partial_i^2\mathcal V$ vanishes, and adjoining $\dot\zeta=-\lambda\sum_i\partial_i^2\mathcal V$ makes $\mathcal V+\tfrac12Q_\lambda\lambda^2+\tfrac12Q_\eta\sum_i\eta_i^2-D\zeta$ a first integral.

## Expansion

Invariance of a density $\rho$ under a vector field $F$ means $\operatorname{div}(\rho F)=0$, i.e. $F\cdot\nabla\ln\rho+\operatorname{div}F=0$. Here $\operatorname{div}F=-\lambda\sum_i\partial_i^2\mathcal V$, since $\dot\lambda$ does not depend on $\lambda$ and $\dot\eta_i$ does not depend on $\eta$. Along $F$, $-D\,F\cdot\nabla\ln\rho$ equals $\sum_i\partial_i\mathcal V(-\lambda\partial_i\mathcal V+\eta_i)+\lambda\sum_i[(\partial_i\mathcal V)^2-D\partial_i^2\mathcal V]-\sum_i\eta_i\partial_i\mathcal V=-D\lambda\sum_i\partial_i^2\mathcal V$, which cancels the divergence exactly. This is a Nosé–Hoover-type thermostat: $\lambda$ adjusts the dissipation so that the configurational "temperature" matches $D$, and the $\eta_i$ prevent the flow from freezing at equilibria of $\mathcal V$, which a pure gradient flow with variable rate would do.

## Sources

- A. A. Samoletov, B. N. Vasiev, "On the noise modelling in a nerve fiber", arXiv:1105.2396 (2011), Section 3, extended dynamics with feedback functions $g$, $h_i$, Lemma 1, Theorem 2, Lemma 3 and Theorem 4, <https://doi.org/10.48550/arXiv.1105.2396>.

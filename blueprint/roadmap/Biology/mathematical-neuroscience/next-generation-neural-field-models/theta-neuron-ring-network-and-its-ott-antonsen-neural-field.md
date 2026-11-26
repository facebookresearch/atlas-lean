# Theta-neuron ring network and its Ott–Antonsen neural field

Consider $N$ theta neurons equally spaced on a ring:

$$
\dot\theta_j = 1 - \cos\theta_j + (1 + \cos\theta_j)(\eta_j + \kappa I_j),
\qquad
I_j = \frac{2\pi}{N} \sum_{k=1}^N K\!\left(\tfrac{2\pi(j-k)}{N}\right) P_n(\theta_k).
$$

The pulse is $P_n(\theta) = a_n (1 - \cos\theta)^n$, normalized by $\int_0^{2\pi} P_n = 2\pi$. The coupling kernel $K$ is $2\pi$-periodic, for example $K(x) = (1 + A\cos x)/(2\pi)$. The excitabilities $\eta_j$ are i.i.d. Lorentzian with centre $\eta_0$ and half-width $\gamma > 0$.

In the limit $N \to \infty$, the Ott–Antonsen ansatz gives the long-time dynamics in terms of a local complex order parameter $z(x,t) \in \overline{\mathbb{D}}$, the local average of $e^{i\theta}$ near position $x \in [0, 2\pi)$:

$$
\partial_t z = \frac{(i\eta_0 - \gamma)(1+z)^2 - i(1-z)^2}{2} + \frac{i\kappa}{2}(1+z)^2\, (K * H_n(z)),
$$

where $(K * \varphi)(x) = \int_0^{2\pi} K(x-y)\varphi(y)\,dy$ and $H_n(z)$ is the real polynomial in $z, \bar z$ obtained by averaging $P_n$ over the Poisson kernel. For $n = 2$,

$$
H_2(z) = \tfrac{2}{3}\Big[\tfrac{3}{2} - (z + \bar z) + \tfrac{1}{4}(z^2 + \bar z^2)\Big].
$$

Through the equivalence of theta neurons with quadratic integrate-and-fire neurons, set $w = (1 - \bar z)/(1 + \bar z)$. Then $\pi^{-1}\operatorname{Re} w$ is the instantaneous firing rate at $x$, and $\operatorname{Im} w$ is the mean voltage.

## Expansion

Each theta neuron is the normal form of a saddle-node-on-invariant-circle bifurcation. Its vector field is a first-degree trigonometric polynomial in $\theta$, so the family of Poisson-kernel (Ott–Antonsen) densities is invariant and attracting for Lorentzian heterogeneity. On it, the density at $x$ is determined by one complex number $z(x,t)$, and the Lorentzian average is evaluated by residues at $\eta_0 + i\gamma$. The result is an exact integro-differential equation. It is a "next generation" neural field because it is derived from spiking dynamics rather than postulated as an Amari-type rate equation. Unlike classical one-population neural fields, it supports stable time-periodic bump states, for example with $A = -5$, $\kappa = 1$ and $\gamma = 0.01$.

## Sources

- Laing CR, Omel'chenko OE. Periodic solutions in next generation neural field models. *Biological Cybernetics* 117 (2023) 259–274. <https://doi.org/10.1007/s00422-023-00969-6>. PMCID: PMC10600056.

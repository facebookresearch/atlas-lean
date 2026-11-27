# Unique stable limit cycle of an aligned periodic domain sequence in piecewise-affine gene networks

**Model (Glass networks).** Concentrations $x \in \mathbb{R}_+^n$ of $n$ gene products evolve as

$$\dot x = \kappa(x) - \Gamma x,$$

where $\Gamma = \mathrm{diag}(\gamma_1, \dots, \gamma_n)$ holds positive degradation rates and $\kappa$ is piecewise constant, depending on $x$ only through step functions $\mathsf{s}^\pm(x_i, \theta_i)$ at thresholds $0 < \theta_i^1 < \dots < \theta_i^{q_i - 1}$. The thresholds cut the state space into rectangular regular domains $a$; inside $a$ the flow is affine and converges toward the *focal point* $\phi(a) = \Gamma^{-1}\kappa(a)$, leaving $a$ through a facet in some exit direction. Transition maps between entry and exit facets are explicit and act by $x_k \mapsto \phi_k + (x_k - \phi_k)\big(\frac{\phi_s - \theta_s}{\phi_s - x_s}\big)^{\gamma_k/\gamma_s}$ in the exit direction $s$.

**Theorem.** Let $\mathcal{C} = \{a^0, \dots, a^{\ell - 1}\}$ be a sequence of regular domains visited periodically by the flow, each $a^i$ with a unique exit direction $s_i$, such that every variable switches at least once along $\mathcal{C}$ and successive focal points are *aligned* ($\phi_j^{i+1} = \phi_j^i$ for all $j \ne s_{i+1}$). Let $T: W^0 \to W^0$ be the first-return map to the entry wall $W^0$ of $a^0$, in coordinates where the periodic boundary point is $0$, and $\lambda = \rho\big(DT(0)\big)$. Then:
1. if $\lambda \le 1$, $T^n x \to 0$ for every $x \in W^0$ (trajectories spiral into the threshold intersection);
2. if $\lambda > 1$, $T$ has a unique nonzero fixed point $q$, lying in the interior of the region that all orbits enter, and $T^n x \to q$ for every $x \in W^0 \setminus \{0\}$, so the network has a unique limit cycle through $\mathcal{C}$, which attracts all trajectories through $W^0$ except the fixed point $0$.
If in some direction two distinct thresholds are crossed along $\mathcal{C}$, conclusion 2 always holds.

**Fixed-point lemma (Smith).** Let $T: [0, p] \to [0, p]$ be continuous, $C^1$ on $(0, p)$, with $DT(0)$ existing as a limit, $Tp < p$, $T$ strongly monotone ($DT(x) > 0$) and concave ($DT(y) \lneq DT(x)$ for $0 < x < y < p$). If $T0 = 0$, then $\rho(DT(0)) \le 1$ gives $T^n x \to 0$ for all $x$, and $\rho(DT(0)) > 1$ gives a unique nonzero fixed point attracting $[0,p] \setminus \{0\}$.

## Proof sketch

The return map is a composition of the local transition maps along the cycle. Each has a Jacobian with fixed sign pattern, nonzero only on the diagonal and in the column of the exit variable, so the composite Jacobian is positive once every variable has switched; a sign-pattern change of coordinates makes $T$ monotone. Second derivatives of the local maps have the sign needed for concavity, which is where alignment of focal points is used. Smith's theorem for monotone concave maps then gives the dichotomy governed by the spectral radius at the fixed point $0$. This extends earlier single-loop results (cyclic negative feedback) to networks with several interaction loops, giving a computable criterion for sustained oscillations in idealized gene regulatory models.

## Sources

- Etienne Farcot and Jean-Luc Gouzé, "Limit cycles in piecewise-affine gene network models with multiple interaction loops", *International Journal of Systems Science* 41 (2010), 119–130, <https://doi.org/10.1080/00207720903144552>. Preprint version: arXiv:0903.1969 (2009), Section 2 (piecewise-affine models and transition maps), Theorem 1 (quoted from H. L. Smith), Propositions 1–3, Assumption 1 and Theorem 2 (Section 3), <https://doi.org/10.48550/arXiv.0903.1969>.

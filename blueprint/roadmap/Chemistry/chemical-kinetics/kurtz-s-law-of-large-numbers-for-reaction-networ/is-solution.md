# Solution of the mean-field equation of a reaction network

Let $G$ be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with
species set $S$ and finite reaction set $\rho$, and for each reaction $r$ let
$\beta_r \colon \mathbb{R}^S \to \mathbb{R}$ be a real function, the macroscopic rate function of
$r$; no sign or regularity is required of it. A path $x \colon \mathbb{R} \to \mathbb{R}^S$ solves
the mean-field (deterministic reaction-rate) equation on $t \ge 0$ if for every $t \ge 0$ and every
species $i$ the coordinate $x_i$ is differentiable at $t$ with

$$x_i'(t) = \sum_{r \in \rho} \beta_r(x(t))\, \zeta_r(i),$$

where $\zeta_r = \mathrm{prod}(r) - \mathrm{src}(r)$ is the [reaction vector](reaction-vector.md) of
$r$. The derivative is two-sided, also at $t = 0$, so the condition at $0$ involves values of $x$ at
negative times; nothing else is required there. For finite $S$ and mass-action rates
$\beta_r(u) = \kappa_r \prod_{s \in S} u_s^{\mathrm{src}(r)_s}$, the right side is the
[mass-action vector field](../../../Dynamics/smooth-dynamics/mass-action-field.md) of $G$ with rate
constants $\kappa$.

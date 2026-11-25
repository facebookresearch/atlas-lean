# Pseudo-Helmholtz function along positive mass-action solutions

Let $N$ be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with finite species set $S$ and finite reaction set $\rho$, let $k \in \mathbb{R}^\rho$ and $c^* \in \mathbb{R}^S$, and let
$x \colon \mathbb{R} \to \mathbb{R}^S$ have derivative $f(x(t))$ at $t$, where $f$ is the [mass-action vector field](../../../Dynamics/smooth-dynamics/mass-action-field.md).
If $x_s(t) > 0$ for every $s$, then $\tau \mapsto G(x(\tau))$ has derivative
$\sum_s (\log x_s(t) - \log c^*_s)\, f_s(x(t))$ at $t$, the
[rate of change of the pseudo-Helmholtz function](helmholtz-rate.md) $G$ relative to $c^*$.

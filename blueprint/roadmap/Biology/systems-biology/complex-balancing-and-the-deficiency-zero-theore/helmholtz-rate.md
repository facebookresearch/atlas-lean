# Rate of change of the pseudo-Helmholtz function

Let $N$ be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with finite species set $S$ and finite reaction set $\rho$, let $k \in \mathbb{R}^\rho$ be rate constants and $c^*, c \in \mathbb{R}^S$. The rate of
change of the pseudo-Helmholtz function along the [mass-action vector field](../../../Dynamics/smooth-dynamics/mass-action-field.md) $f$ is

$$\sum_{s \in S} (\log c_s - \log c^*_s)\, f_s(c),$$

with the conventions $\log 0 = 0$ and $\log x = \log|x|$ for $x < 0$. For positive $c$ and $c^*$ it is the derivative of the
[pseudo-Helmholtz function](pseudo-helmholtz.md) at $c$ in the direction $f(c)$
([along solutions](has-deriv-at-pseudo-helmholtz.md)).

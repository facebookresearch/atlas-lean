# The pseudo-Helmholtz function does not increase along solutions

Let $N$ be a [chemical reaction network](reaction-network.md) with finite species set $S$ and finite reaction set $\rho$, let $k_r > 0$ be rate constants and let $c^* \in \mathbb{R}_{>0}^S$ be [complex balanced](is-complex-balanced.md) for $k$. Let $x \colon \mathbb{R} \to \mathbb{R}^S$ have derivative $f(x(t))$ at every
$t \ge 0$, where $f$ is the [mass-action vector field](mass-action-field.md), and suppose $x_s(t) > 0$ for all $s$ and all $t \ge 0$. Then
$t \mapsto G(x(t))$ is nonincreasing on $[0, \infty)$, where $G$ is the
[pseudo-Helmholtz function](pseudo-helmholtz.md) relative to $c^*$.

## Sources

- F. Horn and R. Jackson, *General mass action kinetics*, Arch. Rational Mech. Anal. 47 (1972) 81–116.

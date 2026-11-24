# Gaussian law of the projections of the moment-estimator limit

Let $\sigma$, $a$, $b$ be real, $\mu_X$ a measure on $\mathbb{N}$, $g_\sigma$ the
[moment estimating function](mom-est-fun.md) and $J = J(a, b, \sigma)$ the
[moment Jacobian](mom-jacobian.md), and put
$v(t) = \int \langle g_\sigma((a, b), k), t \rangle^2\, d\mu_X(k)$ for $t \in \mathbb{R}^2$, a
Bochner integral ($0$ for a non-integrable integrand). Let $Y$ be a random vector in $\mathbb{R}^2$
on a measure space $(\Omega', P')$ with $\langle Y, t \rangle \sim N(0, v(t))$ under $P'$ for every
$t \in \mathbb{R}^2$ (which forces $P'$ to be a probability measure). Then for every
$u \in \mathbb{R}^2$

$$\langle -J^{-1} Y, u \rangle \sim N\bigl(0, v\bigl((J^{-1})^{\mathsf T} u\bigr)\bigr),$$

where $J^{-1}$ is the inverse of $J$ when $J$ is invertible, as for $a, b, \sigma > 0$, and $0$
otherwise (the convention of the total inverse), and $(J^{-1})^{\mathsf T}$ is its adjoint.

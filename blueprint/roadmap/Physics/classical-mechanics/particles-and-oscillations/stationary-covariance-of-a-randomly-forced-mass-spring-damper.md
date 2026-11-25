# Stationary covariance of a randomly forced mass–spring–damper

Let $m, c, k > 0$ and $\sigma \ne 0$. Consider the mass–spring–damper driven by white noise,

$$
m\,\ddot x + c\,\dot x + k\,x = \sigma\,\xi(t),
$$

written as the linear stochastic differential equation $dX = A X\,dt + B\,dW$ for the state $X = (x, \dot x)$, with a standard Brownian motion $W$ and

$$
A = \begin{pmatrix} 0 & 1 \\ -k/m & -c/m \end{pmatrix}, \qquad B = \begin{pmatrix} 0 \\ \sigma/m \end{pmatrix}.
$$

**Theorem.** The matrix $A$ is Hurwitz. The stationary law of $X$ has mean zero and covariance

$$
\Sigma = \begin{pmatrix} \dfrac{\sigma^2}{2ck} & 0 \\[1ex] 0 & \dfrac{\sigma^2}{2cm} \end{pmatrix}.
$$

So in the stationary regime, displacement and velocity are uncorrelated, with variances $\sigma^2/(2ck)$ and $\sigma^2/(2cm)$.

**Proof.** The characteristic polynomial of $A$ is $\lambda^2 + (c/m)\lambda + k/m$, and both of its coefficients are positive, so both roots have negative real part. For a linear stochastic differential equation with Hurwitz drift matrix, the stationary covariance is the unique solution of the Lyapunov equation $A\Sigma + \Sigma A^\top + BB^\top = 0$. Write $\Sigma = \begin{pmatrix} p & q \\ q & r \end{pmatrix}$. The three independent entries of the Lyapunov equation give:
- $2q = 0$;
- $r - (k/m)p - (c/m)q = 0$;
- $-2(k/m)q - 2(c/m)r + \sigma^2/m^2 = 0$.

Hence $q = 0$, $r = \sigma^2/(2cm)$ and $p = (m/k)\,r = \sigma^2/(2ck)$.

Solving the Lyapunov equation alone does not show that a stationary process exists. That step needs the stationary law of the vector Ornstein–Uhlenbeck process.

## Depends on

- [Ornstein–Uhlenbeck process](../../../Probability/stochastic-calculus/ornstein-uhlenbeck-process/README.md)

## Background

- [Variance of the stationary damper response is σ² / (2 c k)](random-response-of-a-first-order-mechanical-syst/stationary-response-variance.md)
- [Exponential stability of linear differential equations](../../../Analysis/ordinary-differential-equations/stability-of-linear-systems/asymptotic-stability-linear-differential-equations.md)

## Expansion

This page becomes ready once these prerequisites are stated:

- Stationary law of the vector Ornstein–Uhlenbeck process: for Hurwitz $A$, the process $dX = AX\,dt + B\,dW$ has a unique stationary Gaussian law, with mean zero and covariance equal to the solution of $A\Sigma + \Sigma A^\top + BB^\top = 0$. It is planned as [Stationary law of a linear stochastic system and the Lyapunov equation](../../../Probability/stochastic-calculus/multidimensional-ornstein-uhlenbeck-process/stationary-law-of-a-linear-stochastic-system-and-the-lyapunov-equation.md), which is not yet ready (statement prerequisite).

## Sources

- S. Särkkä and A. Solin, *Applied Stochastic Differential Equations*, Cambridge University Press, 2019, author copy <https://users.aalto.fi/~asolin/sde-book/sde-book.pdf>, Section 6.5: a stationary solution of $dx = Fx\,dt + L\,d\beta$ exists only for Hurwitz $F$; its stationary mean is zero and its covariance solves $FP + PF^\top + LQL^\top = 0$, equations (6.68)–(6.69); and the stationary covariance function is given in (6.72). The mass–spring–damper instance is computed here.

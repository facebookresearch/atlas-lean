# Limit covariance of the SIR diffusion approximation

For real $\beta$, $\gamma$, a path $x : \mathbb{R} \to \mathbb{R}^2$ and $V_0$, a map $V$ from
$\mathbb{R}$ to symmetric $2 \times 2$ matrices, stored as triples $(V_{11}, V_{12}, V_{22})$, is a
limit covariance around $x$ from $V_0$ if $V(0) = V_0$ and, at every $t \ge 0$,

$$V'(t) = DF(x(t))\, V(t) + V(t)\, DF(x(t))^{\mathsf T} + G(x(t)),$$

the [Lyapunov field](lyapunov-field.md), with the derivative taken within $[0, \infty)$: one-sided
at $t = 0$, and the values of $V$ at negative times play no role. For $\beta, \gamma \ge 0$ and $x$
continuous on an interval $[0, T]$, $V(t)$ at each $t \in [0, T]$ is the covariance of $U(t)$, where
$U$ solves $dU = DF(x(t))\, U\, dt + dM$ on $[0, T]$, $M$ is a continuous centered Gaussian
martingale with $d\langle M \rangle = G(x(t))\, dt$, and $U(0)$ is centered Gaussian with covariance
$V_0$, independent of $M$: see the [Gaussian limit](has-gaussian-law-is-fluctuation-path.md).

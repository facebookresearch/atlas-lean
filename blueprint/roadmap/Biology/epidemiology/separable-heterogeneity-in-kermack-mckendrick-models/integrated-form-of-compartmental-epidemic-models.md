# Integrated form of compartmental epidemic models

**Kermack–McKendrick model.** In a closed population of size $N$, let $S(t)$ be the number of susceptibles and $F(t)$ the force of infection, with

$$\frac{dS}{dt} = -FS, \qquad F(t) = \int_0^\infty A(\tau)\, F(t-\tau)\, S(t-\tau)\, d\tau,$$

where $A(\tau) \ge 0$ is the expected contribution to the force of infection of an individual infected $\tau$ time units ago. Assume $F$ is negligible in the infinite past and $S(-\infty) = N$, and let $w(t) = \int_{-\infty}^t F(\sigma)\, d\sigma$ be the cumulative force of infection. Then $S(t) = N e^{-w(t)}$ and $w$ solves the renewal equation

$$w(t) = \int_0^\infty A(\tau)\, \Psi\bigl(w(t-\tau)\bigr)\, d\tau, \qquad \Psi(w) = N(1 - e^{-w}).$$

**Proposition (reduction to ODEs).** Suppose $A(\tau) = U e^{\tau\Sigma} V$ for a $1 \times n$ row vector $U$, an $n \times 1$ column vector $V$ and an $n \times n$ matrix $\Sigma$ whose eigenvalues all have negative real part. Then $Q(t) = \int_0^\infty e^{\tau \Sigma} V\, \Psi(w(t-\tau))\, d\tau$ satisfies the closed $n$-dimensional system (the **integrated form**)

$$\frac{dQ}{dt} = \Sigma Q + V\, \Psi(UQ), \qquad w = UQ.$$

Conversely, let $Q$ be a solution on all of $\mathbb R$ that satisfies the past boundary condition $\lim_{s \to -\infty} e^{(t-s)\Sigma} Q(s) = 0$ for every $t$ (for instance, $Q$ bounded on $(-\infty, 0]$). Then $Q(t) = \int_0^\infty e^{\tau \Sigma} V\, \Psi(UQ(t-\tau))\, d\tau$ and $w = UQ$ solves the renewal equation. Without the past boundary condition the converse fails: for $N = U = V = 1$ and $\Sigma = -1$ the ODE admits $Q(0) = 2$, whereas $\Psi \le 1$ gives $\int_0^\infty e^{-\tau}\Psi(w(-\tau))\,d\tau \le 1$ for every history. This corrects the converse as printed after (3.5), "given a solution of (3.5), we can define w by (3.4) and verify that w satisfies (2.5)", which is stated for every solution: for that solution $w(0) = UQ(0) = 2$, while the right-hand side of (2.5) is at most $1$. With $Y(t) = \int_0^\infty e^{\tau\Sigma} V F(t-\tau) S(t-\tau)\, d\tau$, the **standard form** $\dot S = -FS$, $\dot Y = \Sigma Y + (FS)V$, $F = UY$ holds, and $Q(t) = \int_{-\infty}^t Y(\sigma)\, d\sigma$.

**Examples.** For SIR, $\dot S = -\beta IS$, $\dot I = -\alpha I + \beta IS$, the integrated form is $\dot Q = -\alpha Q + \Psi(\beta Q)$ with $Q = \int_{-\infty}^t I$. For SEIR the integrated form is $\dot Q_1 = -\gamma Q_1 + \Psi(\beta Q_2)$, $\dot Q_2 = \gamma Q_1 - \alpha Q_2$, with $V = (1, 0)^\top$, $U = (0, \beta)$ and $\Sigma = \begin{pmatrix} -\gamma & 0 \\ \gamma & -\alpha \end{pmatrix}$.

## Proof depends on

- [Duhamel's formula (variation of constants)](../../../Analysis/ordinary-differential-equations/duhamel-variation-of-constants.md): for the converse, write $Q(t) = e^{(t-s)\Sigma}Q(s) + \int_s^t e^{(t-\sigma)\Sigma} V \Psi(UQ(\sigma))\, d\sigma$ and let $s \to -\infty$.

## Expansion

Integrating $F = \int A F S$ over $(-\infty, t]$ and using $FS = -\dot S$ gives the renewal equation, since $N - S = \Psi(w)$. When $A$ has the state representation $U e^{\tau\Sigma} V$ (newly infected individuals enter state $V$, progress by the Markov generator $\Sigma$ and infect at rates $U$), differentiating $Q$ gives $\dot Q = \Sigma Q + V\Psi(w)$, and the renewal equation reads $w = UQ$. The integrated form has dimension $n$ rather than $n + 1$; its main advantage is that it extends to separable heterogeneity simply by changing $\Psi$. Only for such matrix-exponential kernels does the general Kermack–McKendrick model reduce to finitely many ODEs. For SIR, letting $t \to \infty$ in the integrated form gives $\alpha w_\infty/\beta = \Psi(w_\infty)$, the analogue of the classical [final-size equation](../kermack-mckendrick-sir-model/final-size-eq.md) with $S(-\infty) = N$ in place of $S(0)$.

## Sources

- O. Diekmann and H. Inaba, "A systematic procedure for incorporating separable static heterogeneity into compartmental epidemic models", *Journal of Mathematical Biology* (2023), <https://doi.org/10.1007/s00285-023-01865-0> (PMC9839824; Sections 2–4, Equations (2.1)–(2.6), (3.1)–(3.5) and (4.1)–(4.11)).

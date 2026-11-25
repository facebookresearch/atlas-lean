# Scaled internal clock of a reaction

Let $C$ be a
[stochastic reaction network](../non-explosion-of-stochastic-reaction-networks/stochastic-crn.md) on
a species set $S$, with propensities $\lambda_r \ge 0$. For a natural number $N$, a count path
$X \colon \mathbb{R} \to \mathbb{N}^S$, a reaction $r$ and a real time $t$, the scaled clock of $r$
at time $t$ is

$$\Lambda_r(t) = \frac{1}{N} \int_0^t \lambda_r(X(s))\, ds.$$

The integral is oriented and by convention $0$ when the integrand is not integrable on the interval
between $0$ and $t$. Unlike the [internal clock](clock.md), the scaled clock is not truncated, so
$\Lambda_r(t) \le 0$ for $t < 0$. It is meant for $N \ge 1$, where $N \Lambda_r(t)$ is the internal
clock at every $t \ge 0$; for $N = 0$ the convention $a/0 = 0$ gives $\Lambda_r(t) = 0$.

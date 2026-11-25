# Lévy's characterisation of Brownian motion

Let $(\Omega, P)$ be a probability space with a filtration $F = (F_t)_{t \ge 0}$, and $M = (M_t)_{t \ge 0}$ a real
$F$-martingale with continuous paths and $M_0 = 0$ almost surely, such that $(M_t^2 - t)_{t \ge 0}$ is also an
$F$-martingale. Then $M$ is a Brownian motion, and each increment $M_t - M_s$ ($s \le t$) is independent of
$F_s$. Le Gall states the result for continuous local martingales with quadratic variation
$\langle M, M \rangle_t = t$; this is its special case for martingales, where $\langle M, M \rangle_t = t$ means that
$M_t^2 - t$ is a martingale.

The proof applies Itô's formula for continuous martingales to $\exp(i \xi M_t + \xi^2 t/2)$: these
processes are martingales, which identifies the conditional law of $M_t - M_s$ given $F_s$ as
$N(0, t - s)$.

## Background

- [Itô's formula](ito-formula.md): the formula for a Brownian integrator, a special case of the
  formula for continuous martingales that the proof uses.

## Sources

- J.-F. Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus*, Graduate Texts in Mathematics 274, Springer, 2016, Chapter 5, section "Lévy's characterization of Brownian motion".

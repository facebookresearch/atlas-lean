# Girsanov's theorem for a constant drift

Let $B$ be a real Brownian motion under $P$, $\mu \in \mathbb{R}$ and $T \ge 0$, and let $Q$ be the measure
with density $dQ/dP = \exp(\mu B_T - \mu^2 T/2)$. Then for every finite set $I \subseteq [0, T]$, the
vector $(B_t - \mu t)_{t \in I}$ has under $Q$ the finite-dimensional law of Brownian motion at the times
$I$: under $Q$, the process $B_t - \mu t$, $0 \le t \le T$, has the finite-dimensional laws of Brownian
motion. This is the Cameron–Martin formula for $h(t) = \mu t$, Girsanov's theorem with the drift
$\int_0^t \mu\, ds$.

## Informally uses

- [Lévy's characterisation of Brownian motion](it-s-formula/is-brownian-real-of-martingale-sq-sub.md):
  the proof of Girsanov's theorem checks that $B_t - \mu t$ is a continuous $Q$-martingale with
  quadratic variation $t$, and concludes with Lévy's theorem.

## Background

- [Existence of Brownian motion](construction-and-sample-paths-of-brownian-motion/exists-is-brownian-real.md):
  the Brownian motion that is reweighted.

## Sources

- J.-F. Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus*, Graduate Texts in Mathematics 274, Springer, 2016, Chapter 5, sections "Girsanov's theorem" and "A few applications of Girsanov's theorem".

# Optional stopping theorem in continuous time

Let $\mu$ be a probability measure, $(\mathcal{F}_t)_{t \ge 0}$ a filtration, and
$(M_t)_{t \ge 0}$ a real martingale with continuous paths, and let $\sigma \le \tau$ be stopping
times with $\tau \le n$ for a constant $n$. Then $M_\sigma = \mathbb{E}[M_\tau \mid \mathcal{F}_\sigma]$
almost surely.

## Informally uses

- [Stopped value as conditional expectation of the limit](stopped-value-at-top-ae-eq-cond-exp-limi.md):
  the discrete-time theorem, applied to the dyadic approximations
  $\sigma_k = \lceil 2^k \sigma \rceil / 2^k$ and $\tau_k = \lceil 2^k \tau \rceil / 2^k$, which are
  stopping times decreasing to $\sigma$ and $\tau$; path continuity and uniform integrability
  pass to the limit.

## Background

- [Strong Markov property of Brownian motion](../../stochastic-calculus/strong-markov-property-and-reflection-principle/strong-markov.md):
  the same dyadic approximation of a stopping time is used there.

## Sources

- J.-F. Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus*, Graduate Texts in
  Mathematics 274, Springer, 2016, Chapter 3, section "Optional stopping theorems" (stated there
  for uniformly integrable martingales with right-continuous paths; a martingale on $[0, n]$ is
  uniformly integrable).

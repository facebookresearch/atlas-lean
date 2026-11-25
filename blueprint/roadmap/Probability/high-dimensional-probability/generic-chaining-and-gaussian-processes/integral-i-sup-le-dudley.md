# Dudley's entropy bound

Let $T$ be a finite nonempty metric space and $(X_t)_{t \in T}$ a process of measurable, integrable, centred
random variables on a probability space that satisfies the
[sub-Gaussian increment condition](satisfies-increment-condition.md). Then

$$\mathbb{E}\sup_{t \in T} X_t \le L\sum_{n \ge 0} 2^{n/2} e_n(T)$$

with $L = 17$ (Talagrand, *Upper and Lower Bounds for Stochastic Processes*, 2nd ed., 2021,
Proposition 2.5.1, where $L$ is a universal constant; the bound is due to Dudley). Talagrand
obtains it from (2.34) by taking for $T_n$ a set of at most $N_n$ centres realising $e_n(T)$; here
each $t$ is chained through its nearest centres, whose links have length at most
$e_n(T) + e_{n-1}(T)$, which gives the constant $7(1 + \sqrt 2) < 17$.

## Informally uses

- [The chaining bound for a centred process](of-real-integral-i-sup-le-of-chain.md): the bound
  (2.34), which Talagrand applies to sets realising the entropy numbers.
- [Entropy numbers](entropy-number.md): the quantities of (2.36).

## Background

- [Generic chaining bound](integral-i-sup-le-gamma-two.md): since
  $\gamma_2(T, d) \le L\sum_n 2^{n/2} e_n(T)$ (Talagrand, Exercise 2.7.6), the generic chaining
  bound is never worse than Dudley's up to the constant; for subsets of $\mathbb{R}^m$ it can be
  better by a factor of order $\log(m + 1)$, and no more (Exercises 2.7.9 and 2.7.10).

# Generic chaining bound

Let $T$ be a finite nonempty metric space and $(X_t)_{t \in T}$ a process of measurable, integrable, centred
random variables ($\mathbb{E}X_t = 0$) on a probability space that satisfies the
[sub-Gaussian increment condition](satisfies-increment-condition.md). Then

$$\mathbb{E}\sup_{t \in T} X_t \le L\,\gamma_2(T, d)$$

with $L = 10$ (Talagrand, *Upper and Lower Bounds for Stochastic Processes*, 2nd ed., 2021,
Theorem 2.7.11, where $L$ is an unspecified universal constant). The bound is stated with the
expectation in $[0, \infty]$; the real form is the next page.

The proof follows Talagrand's: for an admissible sequence, choose one point in each cell, chain
every $t$ through these points (Theorem 2.7.2), and bound the chain by the union-bound argument
of Section 2.4. Since $T$ is finite, the chain may end at $t$ itself after
$\operatorname{card} T + 1$ steps. The constant comes out as $7\sqrt 2 < 10$.

## Informally uses

- [The chaining bound for a centred process](of-real-integral-i-sup-le-of-chain.md): Talagrand's
  proof of Theorem 2.7.2 applies the bound (2.34) to one point from each cell.
- [Talagrand's $\gamma_\alpha$ functional](gamma-functional.md): Theorem 2.7.11 combines
  Theorem 2.7.2 with Definition 2.7.3.

## Background

- [Dudley's entropy bound](integral-i-sup-le-dudley.md): the classical bound, which the generic
  chaining bound improves (Talagrand, Exercise 2.7.6).
- [Majorizing measure theorem](majorizing-measure.md): for Gaussian processes the bound is sharp
  up to a universal factor.
- [Concentration of Lipschitz functions of Gaussian variables](../../concentration-inequalities/sub-exponential-variables-and-bernstein-s-inequa/lipschitz-concentration-std-gaussian.md):
  the companion fact that $\sup_t X_t$ concentrates around its mean at the scale
  $\sup_t (\mathbb{E}X_t^2)^{1/2}$.

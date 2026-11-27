# Strong solutions of SDEs with Lipschitz coefficients

Let $(\Omega, P)$ be a probability space with a filtration $F$, and $B$ a real Brownian motion with
continuous paths, adapted to $F$, whose increments $B_t - B_s$ ($s \le t$) are independent of $F_s$. Let
$\sigma, b : \mathbb{R} \to \mathbb{R}$ be Lipschitz and $x \in \mathbb{R}$. Call a solution an adapted process $X$
with continuous paths, $\mathbb E \int_0^t X_s^2\, ds < \infty$ for every $t \ge 0$, and, for every $t \ge 0$,
almost surely

$$X_t = x + \int_0^t \sigma(X_s)\, dB_s + \int_0^t b(X_s)\, ds,$$

where $\int_0^t \sigma(X_s)\, dB_s$ is the [$L^2$ Itô integral](it-integral/ito-integral-2.md), whence the
square-integrability condition. Then a solution exists, and any two solutions $X, Y$ are
indistinguishable: almost surely $X_t = Y_t$ for all $t$.

## Informally uses

- [Itô isometry for progressive integrands](it-integral/lintegral-ito-integral-sq-of-is-progress.md):
  controls $\mathbb E (\int (\sigma(X) - \sigma(Y))\, dB)^2$ by $K^2\, \mathbb E \int (X - Y)^2\, ds$ in the Picard
  iteration and in the uniqueness argument.
- [Doob's $L^2$ maximal inequality in continuous time](../martingales/doob-s-maximal-inequalities/lintegral-i-sup-sq-le-of-continuous.md):
  turns the isometry into a bound on $\mathbb E \sup_{s \le t} |\int_0^s \dots dB|^2$, so that the iterates
  converge uniformly on compacts.
- [Continuous modification](it-integral/ito-integral-continuous-modification.md): the solution is
  built from the continuous version of the stochastic integral.

## Background

- [The pathwise Langevin solution is an OU process](ornstein-uhlenbeck-process/is-ornstein-uhlenbeck-from-zero-ou-path.md):
  a linear instance ($\sigma$ constant, $b(x) = -\theta x$), solved explicitly.

## Sources

- J.-F. Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus*, Graduate Texts in Mathematics 274, Springer, 2016, Chapter 8, section "The Lipschitz case".
- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer, 1991,
  Section 5.2.

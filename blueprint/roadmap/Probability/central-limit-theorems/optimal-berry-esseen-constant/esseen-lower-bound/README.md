# Esseen's lower bound for the Berry–Esseen constant

Let $C_0$ be the optimal Berry–Esseen constant for identically distributed summands, the infimum of all real $C$ such that for every probability measure $\mu$ on $\mathbb{R}$ with
mean $0$, variance $1$ and finite third absolute moment $\rho = \int |x|^3 \, d\mu$, and every integer
$n \ge 1$,

$$\sup_{x \in \mathbb{R}} |F_n(x) - \Phi(x)| \le \frac{C \rho}{\sqrt{n}},$$

where $F_n$ is the distribution function of $(X_1 + \dots + X_n)/\sqrt{n}$ for independent random
variables $X_1, \dots, X_n$ with law $\mu$, and $\Phi$ is the standard normal distribution function.
Then

$$C_0 \ge \frac{\sqrt{10} + 3}{6\sqrt{2\pi}} \approx 0.4097.$$

## Idea

An upper bound on $C_0$ needs a proof covering every law; a lower bound needs only one bad example.
Esseen found it among two-point laws. For a law on two points with mean $0$ and variance $1$, the
normalized sums take values in a lattice, and the asymptotic expansion of their distribution functions
has a correction of order $1/\sqrt{n}$ that combines the skewness of the law with a lattice term coming
from the jumps. For a suitably chosen two-point law, this correction makes the distance to $\Phi$,
multiplied by $\sqrt{n}/\rho$, have limit superior at least $(\sqrt{10} + 3)/(6\sqrt{2\pi})$ as
$n \to \infty$; the jumps alone give less. No admissible constant can therefore be
smaller. The constant is positive, as one statement of the card records. Together with
Shevtsova's upper bound $C_0 \le 0.4748$, it locates the optimal constant within an interval of length
about $0.07$.

## Statements

- [Esseen's lower bound for the Berry–Esseen constant](esseen1956-lower-bound-holds.md)
- [Statement of Esseen's lower bound for the Berry–Esseen constant](esseen1956-lower-bound.md): statement
- [Esseen's lower-bound constant](esseen-constant.md): definition of the constant in the main statement
- [Esseen's lower-bound constant is positive](esseen-constant-positive.md): basic property of the constant

## Background

- [The optimal Berry–Esseen constant](../optimal-constant/README.md): the constant $C_0$ bounded here.

## Sources

- C.-G. Esseen, "A moment inequality with an application to the central limit theorem",
  Skandinavisk Aktuarietidskrift (1956).

# Selection density on neutral path space without stochastic integrals

Let $X$ be the [continuous neutral Wright–Fisher process](continuous-realization-2.md) on $[0, 1]$, without mutation, with generator $L_0 f(x) = \tfrac12 x(1 - x) f''(x)$, and let $\alpha \in \mathbb R$. Then

$$Z^\alpha_t = \exp\Bigl(\alpha (X_t - X_0) - \frac{\alpha^2}{2} \int_0^t X_s (1 - X_s)\, ds\Bigr), \qquad t \ge 0,$$

is a positive martingale with $\mathbb E\, Z^\alpha_t = 1$ for all $t$. It is the [exponential martingale of a positive test function](../../../../Probability/markov-chains/martingale-problems/exponential-martingale-for-positive-test-functio.md) $g(x) = e^{\alpha x}$, since $L_0 g = \frac{\alpha^2}{2} x(1 - x)\, g$, so that $g(X_t)/g(X_0)\, \exp\bigl(-\int_0^t (L_0 g/g)(X_s)\, ds\bigr) = Z^\alpha_t$. No stochastic integral is used. For $\alpha = 0$, $Z^0 \equiv 1$, and $0 < Z^\alpha_t \le e^{|\alpha|}$ for all $t$.

## Depends on

- [Exponential martingale for positive test functions in a martingale problem](../../../../Probability/markov-chains/martingale-problems/exponential-martingale-for-positive-test-functio.md)
- [Continuous modification selected by Kolmogorov's theorem](continuous-realization-2.md)

## Expansion

A full proof page must still establish:

- that the neutral process solves the martingale problem for $L_0$ on a domain containing $g(x) = e^{\alpha x}$;
- the identity $L_0 g / g = \frac{\alpha^2}{2} x(1-x)$ and the resulting form of $Z^\alpha$;
- the bound $Z^\alpha_t \le e^{|\alpha|}$, from $|X_t - X_0| \le 1$ and the nonnegativity of the integral.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley, 1986, Chapter 4 (change of measure), <https://doi.org/10.1002/9780470316658>
- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer, 1991, Girsanov's theorem, <https://doi.org/10.1007/978-1-4612-0949-2> (background)

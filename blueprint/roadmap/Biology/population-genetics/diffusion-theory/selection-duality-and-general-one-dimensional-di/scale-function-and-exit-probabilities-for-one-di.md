# Scale function and exit probabilities for one-dimensional diffusions (process level)

Let $X$ be a continuous $[l, r]$-valued solution of the martingale problem for $L = b\, \frac{d}{dx} + \frac{1}{2} a\, \frac{d^2}{dx^2}$, with $a$ and $b$ continuous on $(l, r)$ and $a > 0$ there, so that $s$ below is $C^2$ on $(l, r)$ with $Ls = 0$, and let

$$s(x) = \int_c^x \exp\Bigl(-\int_c^y \frac{2 b}{a}\Bigr)\, dy$$

be its increasing scale function, for some $c \in (l, r)$. Suppose that $s(l)$ and $s(r)$ are finite, and that the exit time $\tau = \inf\{t : X_t \in \{l, r\}\}$ satisfies $\mathbb{P}_x(\tau < \infty) = 1$: an endpoint is actually hit, not only approached. Then

$$\mathbb{P}_x(X_\tau = r) = \frac{s(x) - s(l)}{s(r) - s(l)}, \qquad x \in (l, r).$$

The hitting hypothesis holds, for instance, when both endpoints are accessible in the sense of the Feller boundary classification.

## Proof depends on

- [Strong solutions solve the martingale problem](../../../../Probability/markov-chains/martingale-problems/strong-solutions-solve-the-martingale-problem.md)
- [Optional stopping theorem in continuous time](../../../../Probability/martingales/optional-stopping-theorem/stopped-value-ae-eq-cond-exp-of-le-of-co.md)

## Expansion

1. $s(X_t)$ is a local martingale up to $\tau$, by the martingale problem with $L s = 0$ and [optional stopping](../../../../Probability/martingales/optional-stopping-theorem/stopped-value-ae-eq-cond-exp-of-le-of-co.md) at exit times of compact subintervals. The ratio follows from bounded convergence.
2. The guards. For $dX = X(1 - X)\, dB$ on $(0, 1)$, $s(x) = x$ is finite at both ends but $0$ and $1$ are inaccessible and $\mathbb{P}(T_1 < T_0) = 0$, which the hitting hypothesis excludes. For $dX = \frac{1}{2} X\, dt + X\, dB$, $s(0) = -\infty$ and no ratio is claimed.
3. A check: for Brownian motion with drift $\mu \ne 0$, $s(x) = (1 - e^{-2\mu x})/(2\mu)$, and for $\mu = 0$, $s(x) = x$.

## Sources

- S. Karlin and H. M. Taylor, *A Second Course in Stochastic Processes*, Academic Press (1981), <https://shop.elsevier.com/books/a-second-course-in-stochastic-processes/karlin/978-0-08-057050-1> (scale function).

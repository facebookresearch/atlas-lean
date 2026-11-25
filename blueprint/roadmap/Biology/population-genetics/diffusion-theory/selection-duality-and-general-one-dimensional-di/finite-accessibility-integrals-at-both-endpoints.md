# Accessible endpoints give almost sure exit with finite mean exit time

Let $X$ be a continuous $[l, r]$-valued solution of the martingale problem for $L = b\, \frac{d}{dx} + \frac{a}{2} \frac{d^2}{dx^2}$, with $a > 0$ and $b$ continuous on $(l, r)$, scale function $s$ and speed measure $m$. Suppose both endpoints are accessible: for some $c \in (l, r)$, $\Sigma(l) = \int_l^c (s(y) - s(l))\, m(dy) < \infty$ and $\Sigma(r) = \int_c^r (s(r) - s(y))\, m(dy) < \infty$ (Feller's accessibility integrals, which presuppose $s(l)$ and $s(r)$ finite). Then:

1. the weighted integral $\int_l^r (s(y) - s(l))(s(r) - s(y))\, m(dy)$ is finite, by Fubini's theorem, since the factor $s(r) - s(y)$ is bounded near $l$, and symmetrically near $r$;
2. $v(x) = \int G(x, y)\, m(dy)$, with $G$ [the Dirichlet Green's function](green-function.md), is bounded, of class $C^2$ on $(l, r)$, and satisfies $L v = -1$;
3. for the exit times $\tau_n$ of intervals $[l_n, r_n] \uparrow (l, r)$, which are [stopping times](../../../../Probability/markov-chains/finite-continuous-time-markov-chains/hitting-times-of-finite-continuous-time-markov-c/hitting-times-of-closed-sets-by-continuous-adapt.md), [optional stopping](../../../../Probability/martingales/optional-stopping-theorem/stopped-value-ae-eq-cond-exp-of-le-of-co.md), part (a), applied to $v(X_t) + t$ gives $\mathbb{E}_x[t \wedge \tau_n] \le \sup v$.

Hence $\lim_n \tau_n$ is finite almost surely and, by continuity of the paths, equals the hitting time $\tau$ of $\{l, r\}$: $\mathbb{P}_x(\tau < \infty) = 1$ and $\mathbb{E}_x \tau \le \sup v$.

## Depends on

- [Hitting times of closed sets by continuous adapted processes are stopping times (continuous time)](../../../../Probability/markov-chains/finite-continuous-time-markov-chains/hitting-times-of-finite-continuous-time-markov-c/hitting-times-of-closed-sets-by-continuous-adapt.md)
- [Optional stopping theorem in continuous time](../../../../Probability/martingales/optional-stopping-theorem/stopped-value-ae-eq-cond-exp-of-le-of-co.md)
- [Dirichlet Green's function of a one-dimensional diffusion](green-function.md)

## Proof depends on

- [Martingale problems](../../../../Probability/markov-chains/martingale-problems/martingale-problems-generic-definition.md)

## Expansion

1. The three steps above.
2. A check: in the Wright–Fisher case with genic selection the weighted integral is finite, since $s(y) \sim y$ and $m(dy) \sim 2\, dy / y$ near $0$.

## Sources

- S. Karlin and H. M. Taylor, *A Second Course in Stochastic Processes*, Academic Press (1981), Chapter 15 (accessibility and mean exit times).

# Stability of Optimistic Hedge iterates

Let player $i$ run Optimistic Hedge with step size $\eta > 0$ on loss vectors $\ell_i^t \in [0, 1]^{n_i}$, so that $x_i^{t+1}(a) \propto x_i^t(a) \exp\bigl(-\eta\,(2\ell_i^t(a) - \ell_i^{t-1}(a))\bigr)$ on the simplex $\Delta_{n_i}$. Then consecutive iterates have coordinatewise ratios bounded by $\exp(6\eta)$ in both directions:

$$
\max\left\{ \left\lVert \frac{x_i^{t}}{x_i^{t+1}} \right\rVert_\infty,\ \left\lVert \frac{x_i^{t+1}}{x_i^{t}} \right\rVert_\infty \right\} \le \exp(6\eta).
$$

## Proof sketch

Each exponent $-\eta(2\ell_i^t(a) - \ell_i^{t-1}(a))$ lies in $[-2\eta, \eta]$, so the unnormalized factor of every action lies in $[e^{-2\eta}, e^{\eta}]$, and so does the normalizer, which is the $x_i^t$-average of these factors. Hence every ratio $x_i^{t+1}(a)/x_i^t(a)$ lies in $[e^{-3\eta}, e^{3\eta}] \subseteq [e^{-6\eta}, e^{6\eta}]$.

## Depends on

- [Optimistic Hedge in a repeated normal-form game](optimistic-hedge-in-games.md)

## Sources

- C. Daskalakis, M. Fishelson, N. Golowich, "Near-Optimal No-Regret Learning in General Games", NeurIPS 2021, arXiv:2108.06924, update (1) and the proof of Lemma 4.2.

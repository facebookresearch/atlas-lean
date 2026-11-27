# Existence of travelling fronts in a scalar neural field

Consider the scalar neural field

$$\partial_t u(x, t) = -u + \int_{-\infty}^{\infty} J(x - y)\, S(u(y, t))\, dy$$

(Hastings 2017, Section 1, equation (1.4)). Assume that $J$ is nonnegative, even and continuously differentiable, with $J$ and $J'$ integrable and $\int J = 1$, and that $S$ is smooth, bounded and increasing, with exactly three solutions $u_1 < u_2 < u_3$ of $u = S(u)$, where $S'(u_1) < 1$, $S'(u_2) > 1$ and $S'(u_3) < 1$, so that the constant states $u_1$ and $u_3$ are stable and $u_2$ is unstable. Then there are a unique speed $c$ and a monotone profile $U$, unique up to translation, with $U(\xi) \to u_1$ as $\xi \to -\infty$ and $U(\xi) \to u_3$ as $\xi \to \infty$, such that $u(x, t) = U(x - ct)$ is a solution; with this convention $c > 0$ means the profile moves toward $+\infty$, so that the state $u_1$ invades. Ermentrout and McLeod (1993) prove existence and uniqueness of such a monotone front joining the two stable states; since the equation has no negative feedback, its travelling waves are fronts rather than pulses (Hastings 2017, Section 1).

## Expansion

1. The model, and the bistability of the constant states $u_1 < u_2 < u_3$ under the hypotheses above.
2. The travelling-wave equation $-cU' = -U + J * S(U)$ with limits $u_1$ and $u_3$ at $-\infty$ and $+\infty$.
3. Existence of a monotone front by a continuation argument.
4. Uniqueness of the speed $c$ and of the profile up to translation.
5. The sign of $c$, from the profile identity $-c\int_{-\infty}^{\infty} S'(U(\xi))\,U'(\xi)^2\,d\xi = \int_{u_1}^{u_3} (S(u) - u)\, du$ for the increasing profile $U(x - ct)$: $c$ has the sign opposite to $\int_{u_1}^{u_3} (S(u) - u)\, du$, so $u_3$ invades when this integral is positive. Stability of the front is a separate statement.

## Sources

- S. P. Hastings, Existence of travelling pulses in a neural model, Proc. Roy. Soc. Edinburgh Sect. A 147 (2017), 397–427; Section 1 and equation (1.4) in the numbering of the arXiv version, arXiv:1503.04057. <https://doi.org/10.1017/S0308210516000044>
- Original result: G. B. Ermentrout and J. B. McLeod, Existence and uniqueness of travelling waves for a neural network, Proc. R. Soc. Edinb. A 123 (1993), 461–478. <https://doi.org/10.1017/s030821050002583x> The existence of monotone fronts follows Hastings, Section 1.

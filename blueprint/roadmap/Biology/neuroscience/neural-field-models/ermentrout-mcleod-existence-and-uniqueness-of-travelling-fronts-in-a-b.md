# Existence of travelling fronts in a scalar neural field

Consider the scalar neural field
$$\partial_t u(x, t) = -u + \int_{-\infty}^{\infty} J(x - y)\, S(u(y, t))\, dy$$
with a symmetric positive weight function $J$ and a positive, bounded, increasing firing rate $S$. Ermentrout and McLeod proved the existence of travelling fronts $u(x, t) = U(x - ct)$, with $U$ monotone, for a wide variety of such $J$ and $S$; since the equation has no negative feedback, its travelling waves are fronts rather than pulses (Hastings 2015, Section 1, equation (1.4)).

## Expansion

1. The model and the exact hypotheses on $J$ and $S$ of the original paper, including the bistability of $u = J * S(u)$ for constant states: three equilibria $u_1 < u_2 < u_3$ with $u_1$ and $u_3$ stable.
2. The travelling-wave equation $-cU' = -U + J * S(U)$ with limits $u_1$ and $u_3$ at $\mp\infty$.
3. Existence of a monotone front by a continuation argument.
4. Uniqueness of the speed $c$ and of the profile up to translation.
5. The sign of $c$, which is the sign of $\int_{u_1}^{u_3} (S(u) - u)\, du$ when $J$ has integral $1$, and stability of the front, as separate statements.

## Sources

- S. P. Hastings, Existence of travelling pulses in a neural model, 2015, Section 1. <https://arxiv.org/abs/1503.04057>
- Original result: G. B. Ermentrout and J. B. McLeod, Existence and uniqueness of travelling waves for a neural network, Proc. R. Soc. Edinb. A 123 (1993), 461–478. <https://doi.org/10.1017/s030821050002583x> The existence of monotone fronts follows Hastings, Section 1.

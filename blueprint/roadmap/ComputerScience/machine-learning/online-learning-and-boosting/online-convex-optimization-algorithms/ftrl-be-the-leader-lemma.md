# Be-the-leader: FTRL regret is at most regularizer range plus stability

For every run $(x_t)$ of FTRL on $K$ with regularizer $\psi$ and losses $(\ell_t)$, every $u \in K$ and every $T$,

$$
\sum_{t<T}(\ell_t(x_t) - \ell_t(u)) \le \psi(u) - \psi(x_0) + \sum_{t<T}\big(\ell_t(x_t) - \ell_t(x_{t+1})\big).
$$

## Proof sketch

Induct on $T$ to show that the hypothetical sequence $x_1, x_2, \ldots$, which plays the leader including the current loss, has total loss at most that of $u$ plus $\psi(u) - \psi(x_0)$: at each step $x_{T}$ minimizes $\psi + \sum_{s<T}\ell_s$, so its value is at most the value at $x_{T-1}$ or at $u$. Then add and subtract $\ell_t(x_{t+1})$.

## Depends on

- [Follow the regularized leader](follow-the-regularized-leader.md)

## Sources

- Elad Hazan, "Introduction to Online Convex Optimization", MIT Press, 2022.
- Francesco Orabona, "A Modern Introduction to Online Learning", lecture notes, 2019.

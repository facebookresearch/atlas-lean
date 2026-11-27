# FTRL with a strongly convex regularizer: regret $\psi(u) - \psi(x_0) + \sum L_t^2/(2\mu)$

Let $K$ be convex, $\psi$ be $\mu$-strongly convex on $K$ with $\mu > 0$ (with respect to the ambient norm), the losses $\ell_t$ convex on $K$, and suppose $\ell_t(x_t) - \ell_t(y) \le L_t\|x_t - y\|$ for $y \in K$ (for example $\ell_t$ is $L_t$-Lipschitz). Then every FTRL run satisfies, for every $u \in K$,

$$
\sum_{t<T}(\ell_t(x_t) - \ell_t(u)) \le \psi(u) - \psi(x_0) + \sum_{t<T}\frac{L_t^2}{2\mu}.
$$

Tuned form: if $R$ is $\sigma$-strongly convex on $K$ with $R(y) - R(z) \le D^2$ on $K$, $L_t = L$, and $T \ge 1$, then FTRL with $\psi = R/\eta$ for $\eta = \frac{D}{L}\sqrt{2\sigma/T}$ has regret at most $DL\sqrt{2T/\sigma}$. The norm is arbitrary, so the bound covers $\ell_1$, $\ell_2$ or any other geometry, with $L_t$ playing the role of a dual-norm gradient bound.

## Proof sketch

Write $F_t = \psi + \sum_{s<t}\ell_s$, so $x_t$ minimizes the $\mu$-strongly convex $F_t$ over $K$. The be-the-leader telescoping in its strengthened form gives the identity $\sum_{t<T}(\ell_t(x_t) - \ell_t(u)) = \psi(u) - \psi(x_0) + \sum_{t<T}\big(F_{t+1}(x_t) - F_{t+1}(x_{t+1})\big) + F_T(x_T) - F_T(u)$, and $F_T(x_T) - F_T(u) \le 0$. Strong convexity of $F_t$ at its minimizer gives $F_t(x_t) - F_t(x_{t+1}) \le -\frac{\mu}{2}\|x_t - x_{t+1}\|^2$, so $F_{t+1}(x_t) - F_{t+1}(x_{t+1}) \le L_t\|x_t - x_{t+1}\| - \frac{\mu}{2}\|x_t - x_{t+1}\|^2 \le L_t^2/(2\mu)$. (The plain stability term $\ell_t(x_t) - \ell_t(x_{t+1})$ can equal $L_t^2/\mu$, e.g. $\psi(x) = \mu x^2/2$, $\ell_0(x) = -L x$ on $\mathbb{R}$.) The tuned form balances $D^2/\eta$ against $\eta L^2T/(2\sigma)$.

## Depends on

- [Follow the regularized leader](follow-the-regularized-leader.md)

## Proof depends on

- [Be-the-leader: FTRL regret is at most regularizer range plus stability](ftrl-be-the-leader-lemma.md)

## Sources

- Francesco Orabona, "A Modern Introduction to Online Learning", lecture notes, 2019.
- Elad Hazan, "Introduction to Online Convex Optimization", MIT Press, 2022.

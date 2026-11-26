# FTRL with a strongly convex regularizer: regret $\psi(u) - \psi(x_0) + \sum L_t^2/(2\mu)$

Let $K$ be convex, $\psi$ be $\mu$-strongly convex on $K$ with $\mu > 0$ (with respect to the ambient norm), the losses $\ell_t$ convex on $K$, and suppose $\ell_t(x_t) - \ell_t(y) \le L_t\|x_t - y\|$ for $y \in K$ (for example $\ell_t$ is $L_t$-Lipschitz). Then every FTRL run satisfies, for every $u \in K$,

$$
\sum_{t<T}(\ell_t(x_t) - \ell_t(u)) \le \psi(u) - \psi(x_0) + \sum_{t<T}\frac{L_t^2}{2\mu}.
$$

Tuned form: if $R$ is $\sigma$-strongly convex on $K$ with $R(y) - R(z) \le D^2$ on $K$, $L_t = L$, and $T \ge 1$, then FTRL with $\psi = R/\eta$ for $\eta = \frac{D}{L}\sqrt{2\sigma/T}$ has regret at most $DL\sqrt{2T/\sigma}$. The norm is arbitrary, so the bound covers $\ell_1$, $\ell_2$ or any other geometry, with $L_t$ playing the role of a dual-norm gradient bound.

## Proof sketch

Consecutive iterates minimize objectives that differ by the convex function $\ell_t$, and both objectives are $\mu$-strongly convex; comparing the two first-order optimality conditions gives $\mu\|x_t - x_{t+1}\|^2 \le \ell_t(x_t) - \ell_t(x_{t+1}) \le L_t\|x_t - x_{t+1}\|$, hence the stability term is at most $L_t^2/\mu$, and a sharper argument with the strong-convexity gap gives $L_t^2/(2\mu)$. Insert into the be-the-leader lemma. The tuned form balances $D^2/\eta$ against $\eta L^2T/(2\sigma)$.

## Depends on

- [Follow the regularized leader](follow-the-regularized-leader.md)

## Proof depends on

- [Be-the-leader: FTRL regret is at most regularizer range plus stability](ftrl-be-the-leader-lemma.md)

## Sources

- Francesco Orabona, "A Modern Introduction to Online Learning", lecture notes, 2019.
- Elad Hazan, "Introduction to Online Convex Optimization", MIT Press, 2022.

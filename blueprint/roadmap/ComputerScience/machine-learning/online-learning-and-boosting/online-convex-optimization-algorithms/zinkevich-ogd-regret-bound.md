# Zinkevich's regret bound for projected online gradient descent

Let $K$ have diameter at most $D$, let the subgradients satisfy $\|g_t(x)\| \le G$ on $K$, and run projected online gradient descent from $x_0 \in K$. For every $u \in K$ and $T \ge 1$:

1. with $\eta_t = 1/\sqrt{t+1}$, $\sum_{t<T}(f_t(x_t) - f_t(u)) \le \frac{D^2\sqrt{T}}{2} + \left(\sqrt{T} - \frac12\right)G^2$;
2. with the constant step $\eta = D/(G\sqrt{T})$ (for $D, G > 0$), the regret is at most $GD\sqrt{T}$.

## Proof sketch

The projection inequality gives $2\eta_t\langle g_t, x_t - u\rangle \le \|x_t - u\|^2 - \|x_{t+1} - u\|^2 + \eta_t^2 G^2$. Dividing by $2\eta_t$, summing, and using that $1/\eta_t$ is nondecreasing telescopes the distance terms to at most $D^2/(2\eta_{T-1})$; then $\sum_{t<T} 1/\sqrt{t+1} \le 2\sqrt{T} - 1$ gives item 1, and a constant step balances the two terms in item 2.

## Depends on

- [Online convex optimization protocol and projected online gradient descent](online-convex-optimization-and-projected-ogd.md)

## Proof depends on

- [Anytime regret of online gradient descent](../../../not-yet-classified/online-gradient-descent-anytime/ogd-regret-anytime.md)

## Sources

- Martin Zinkevich, "Online Convex Programming and Generalized Infinitesimal Gradient Ascent", Proceedings of the Twentieth International Conference on Machine Learning (ICML), 2003.
- Elad Hazan, "Introduction to Online Convex Optimization", MIT Press, 2022.

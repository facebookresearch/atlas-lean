# Dynamic regret of online gradient descent in terms of comparator path length

Let $K$ be a nonempty closed convex set with diameter at most $D > 0$, let the convex losses $f_t$ have subgradient norms at most $G > 0$ on $K$, and let $u_0, u_1, \ldots \in K$ be any comparator sequence with path length $P_T = \sum_{t < T-1} \|u_{t+1} - u_t\|$. The dynamic regret is $\sum_{t<T}(f_t(x_t) - f_t(u_t))$. For projected online gradient descent and $T \ge 1$:

1. with a fixed step size $\eta > 0$, the dynamic regret against every comparator sequence with $P_T \le L$ is at most

    $$
    \frac{7D^2}{4\eta} + \frac{LD}{\eta} + \frac{T\eta G^2}{2};
    $$

2. with the step size $\eta \approx \sqrt{P/T}$ for $P = P_T + 1$ known in advance, the dynamic regret is $O(\sqrt{T P})$ for fixed $D$ and $G$.

## Proof sketch

Rerun the static one-step inequality with the comparator changing between rounds. The extra term from replacing $u_t$ by $u_{t+1}$ is bounded by $\|x - u_{t+1}\|^2 - \|x - u_t\|^2 \le 2D\|u_{t+1} - u_t\|$, so the telescoping sum picks up $D P_T/\eta$ (or a step-weighted version), and the dynamic regret is at most $(D^2 + 2DP_T)/(2\eta) + \eta G^2 T/2$, which implies item 1. Bounding the cross terms by $D$ times the path length plus boundary terms instead gives twice the dynamic regret at most $3D^2 P/\eta + \eta G^2 T$, and the step $\eta \approx \sqrt{P/T}$ gives item 2.

Explicit constants (derived from the same inequality): with the constant step $\eta = D/(G\sqrt T)$ the dynamic regret is at most $G(D + P_T)\sqrt{T}$; if $P_T \le P$, the step $\eta = \sqrt{D^2 + 2DP}/(G\sqrt{T})$ gives dynamic regret at most $G\sqrt{T(D^2 + 2DP)}$; and with $\eta_t = D/(G\sqrt{t+1})$ the dynamic regret is at most $(\tfrac32 D + P_T)\,G\sqrt{T}$. For a constant comparator ($P_T = 0$) these reduce to static bounds.

## Depends on

- [Online convex optimization protocol and projected online gradient descent](online-convex-optimization-and-projected-ogd.md)

## Proof depends on

- [Zinkevich's regret bound for projected online gradient descent](zinkevich-ogd-regret-bound.md)

## Sources

- Martin Zinkevich, "Online Convex Programming and Generalized Infinitesimal Gradient Ascent", Proceedings of the Twentieth International Conference on Machine Learning (ICML), 2003, Theorem 2.
- Elad Hazan, "Introduction to Online Convex Optimization", 2nd edition, MIT Press, 2022, Theorem 10.1.

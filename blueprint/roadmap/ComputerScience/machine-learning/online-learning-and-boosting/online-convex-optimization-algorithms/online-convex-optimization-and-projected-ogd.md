# Online convex optimization protocol and projected online gradient descent

In online convex optimization over a set $K$ in a real inner product space $E$, in each round $t = 0, 1, \ldots$ a learner plays $x_t \in K$, then a convex loss $f_t$ is revealed and the learner pays $f_t(x_t)$. The regret against a comparator $u \in K$ after $T$ rounds is $\sum_{t<T}(f_t(x_t) - f_t(u))$. Losses enter through subgradients: a map $g_t$ with $f_t(x) + \langle g_t(x), y - x\rangle \le f_t(y)$ for all $x, y \in K$.

A Pythagorean projection onto $K$ is a map $\Pi : E \to K$ with $\|\Pi(y) - z\| \le \|y - z\|$ for all $y \in E$, $z \in K$ (the metric projection onto a nonempty closed convex set is one). Projected online gradient descent with step sizes $\eta_t > 0$ starts at $x_0 \in K$ and sets $x_{t+1} = \Pi(x_t - \eta_t\, g_t(x_t))$.

## Sources

- Martin Zinkevich, "Online Convex Programming and Generalized Infinitesimal Gradient Ascent", Proceedings of the Twentieth International Conference on Machine Learning (ICML), 2003.
- Elad Hazan, "Introduction to Online Convex Optimization", MIT Press, 2022.

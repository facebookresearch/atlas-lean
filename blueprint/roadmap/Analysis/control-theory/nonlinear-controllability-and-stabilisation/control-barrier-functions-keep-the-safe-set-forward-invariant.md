# Control barrier functions keep the safe set forward invariant

Let $D \subseteq \mathbb{R}^n$ be open, let $f : D \to \mathbb{R}^n$ and $g : D \to \mathbb{R}^{n \times m}$ be locally Lipschitz, and consider $\dot x = f(x) + g(x) u$. Let $h : D \to \mathbb{R}$ be continuously differentiable, $C = \{x \in D : h(x) \ge 0\}$, and $L_f h = \nabla h \cdot f$, $L_g h = \nabla h^\top g$. Let $\alpha : \mathbb{R} \to \mathbb{R}$ be strictly increasing with $\alpha(0) = 0$ (an extended class-$\mathcal{K}$ function). Call $u$ admissible at $x$ if $L_f h(x) + L_g h(x) u \ge -\alpha(h(x))$.

1. **Forward invariance.** If $k : D \to \mathbb{R}^m$ is locally Lipschitz and $k(x)$ is admissible at every $x \in D$, then every solution of $\dot x = f(x) + g(x)k(x)$ with $x(0) \in C$ stays in $C$ on its whole interval of existence.
2. **Minimal safety filter.** For a nominal input $k_0(x)$, the quadratic program $\min_u \tfrac12\|u - k_0(x)\|^2$ subject to admissibility has, when $L_g h(x) \ne 0$, the unique solution

    $$u^\star(x) = k_0(x) + \frac{\max\big(0,\ -L_f h(x) - L_g h(x) k_0(x) - \alpha(h(x))\big)}{\|L_g h(x)\|^2}\, L_g h(x)^\top ,$$

    and $u^\star(x) = k_0(x)$ when $L_g h(x) = 0$ and $k_0(x)$ is admissible.

Part 1 does not need $\alpha$ to be Lipschitz, nor $\nabla h \ne 0$ on the boundary of $C$; local Lipschitz continuity of the closed loop is used only for existence and uniqueness of solutions, and the Lipschitz continuity of $u^\star$ is a separate question.

**Proof.** For part 1, let $x$ be a solution with $h(x(0)) \ge 0$ and suppose $h(x(t_1)) < 0$ for some $t_1 > 0$. Let $t_0 = \sup\{t \le t_1 : h(x(t)) \ge 0\}$; by continuity $h(x(t_0)) = 0$ and $h(x(t)) < 0$ on $(t_0, t_1]$. The function $\eta(t) = h(x(t))$ is continuously differentiable with $\dot\eta(t) = L_f h + L_g h\, k \ge -\alpha(\eta(t)) > 0$ on $(t_0, t_1]$, because $\alpha$ is negative on negative arguments. By the mean value theorem $\eta(t_1) - \eta(t_0) = \dot\eta(\xi)(t_1 - t_0) > 0$ for some $\xi \in (t_0, t_1)$, contradicting $\eta(t_1) < 0 = \eta(t_0)$. Part 2 is the projection of $k_0(x)$ onto a closed half-space $\{u : a^\top u \ge b\}$ with $a = L_g h(x)^\top \ne 0$: the projection is $k_0$ if $a^\top k_0 \ge b$ and $k_0 + (b - a^\top k_0) a / \|a\|^2$ otherwise.

## Sources

- A. D. Ames, S. Coogan, M. Egerstedt, G. Notomista, K. Sreenath and P. Tabuada, "Control barrier functions: theory and applications", *European Control Conference*, 2019, <https://arxiv.org/abs/1903.11199>, Section II: Definition 1 (forward invariance and safety), Definition 2 (control barrier function with an extended class-$\mathcal{K}_\infty$ function), the admissible set (10), Theorem 2 (a Lipschitz controller with values in that set renders $C$ safe, under $\partial h/\partial x \ne 0$ on $\partial C$), and the quadratic program (CBF-QP) with its closed-form min-norm solution. The mean-value proof without the boundary-regularity hypothesis and the explicit projection formula are on the page.

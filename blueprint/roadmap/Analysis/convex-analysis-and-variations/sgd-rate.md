# Convergence rate of the projected subgradient method

Let $E$ be a real inner product space, $f : E \to \mathbb{R}$, $g_t : E \to E$ ($t \in \mathbb{N}$) with $f(x) + \langle g_t(x), y - x\rangle \le f(y)$ for all $t, x, y$ and $\|g_t(x)\| \le G$, and let $\mathrm{proj}$ be a nonexpansive map fixing $x^\ast$. Let $D > 0$, $G > 0$, $x_0$ with $\|x_0 - x^\ast\| \le D$, and an integer $T \ge 1$. With step $\eta = D/(G\sqrt T)$ and the projected subgradient iterates $x_0, \dots, x_{T-1}$, their average $\bar x$ satisfies $f(\bar x) - f(x^\ast) \le DG/\sqrt T$ (for $T = 1$, $\bar x = x_0$).

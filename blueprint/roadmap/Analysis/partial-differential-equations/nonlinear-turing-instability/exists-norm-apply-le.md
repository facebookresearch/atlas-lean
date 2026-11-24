# On a mode acting through a stable matrix, orbits stay bounded

Let $L \ge 0$, $n \in \mathbb{N}$, and let $M$ be a real $2 \times 2$ matrix with
$\operatorname{tr} M < 0$ and $\det M > 0$. If a family $S = (S(t))_{t \ge 0}$ of bounded linear
operators on $C([0, L], \mathbb{R}^2)$ (sup norm) [acts on the Neumann mode](acts-by-modal-ode.md)
$n$ through the ODE $c' = M c$, then there is a constant $C$ such that for all $w \in \mathbb{R}^2$
and $t \ge 0$

$$\bigl\lVert S(t)\bigl(\cos(k_n \cdot)\, w\bigr) \bigr\rVert \le C \lVert w \rVert.$$

The proof uses the Lyapunov function $V(c) = \det M\, (c_0^2 + c_1^2) + (Mc)_0^2 + (Mc)_1^2$, for
which $V' = 2 \operatorname{tr} M\, ((Mc)_0^2 + (Mc)_1^2) \le 0$ along $c' = M c$.

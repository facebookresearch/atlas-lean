# Picard iterates converge to every global solution of the initial value problem

Let $E$
be a real Banach space, let $f : \mathbb{R} \times E \to E$ be continuous, and let $L \ge 0$ be
such that $f(t, \cdot)$ is $L$-Lipschitz for every $t \in \mathbb{R}$. Fix $t_0 \in \mathbb{R}$
and $x_0 \in E$, and let $(u_n)_{n \ge 0}$ be maps $\mathbb{R} \to E$ with $u_0(t) = x_0$ and
$u_{n+1}(t) = x_0 + \int_{t_0}^{t} f(s, u_n(s))\,ds$ for all $n$ and $t$. If $y : \mathbb{R} \to E$
satisfies $y(t_0) = x_0$ and $y'(t) = f(t, y(t))$ for every $t \in \mathbb{R}$, then
$u_n(t) \to y(t)$ as $n \to \infty$ for every $t \in \mathbb{R}$.

Proof: By the convergence of Picard iterates, the iterates converge pointwise to a global solution
through $x_0$ at $t_0$; by uniqueness of solutions for a Lipschitz right-hand side, it equals $y$.

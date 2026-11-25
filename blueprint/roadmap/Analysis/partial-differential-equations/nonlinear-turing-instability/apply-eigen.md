# A Neumann mode along an eigenvector of M is an eigenfunction of S(t)

Let $L$ be real, $n \in \mathbb{N}$, $M$ a real $2 \times 2$ matrix and $S = (S(t))_{t \ge 0}$ a
family of bounded linear operators on $C([0, L], \mathbb{R}^2)$ that
[acts on the Neumann mode](acts-by-modal-ode.md) $n$ through the ODE $c' = M c$. If
$v \in \mathbb{R}^2$ and $r \in \mathbb{R}$ satisfy $M v = r v$, then for every $t \ge 0$

$$S(t)\bigl(\cos(k_n \cdot)\, v\bigr) = e^{r t} \cos(k_n \cdot)\, v.$$

For $L \ge 0$ and $v \neq 0$ the mode is [nonzero](neumann-mode-ne-zero.md), so it is an
eigenfunction of every $S(t)$ with eigenvalue $e^{rt}$.

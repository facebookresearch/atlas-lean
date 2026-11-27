# Solution of the Galerkin system

Let $0 = x_0 < \dots < x_n = 1$ be a partition of $[0, 1]$ and $f : \mathbb{R} \to \mathbb{R}$. A
vector $c \in \mathbb{R}^{n+1}$ solves the Galerkin system if $c_0 = c_n = 0$ and
$(Kc)_j = F_j$ at every interior node $j$, where $K$ is the [stiffness matrix](stiffness.md) and
$F$ the [load vector](load.md). The Galerkin solution is then the [P1 function](p1.md) $u_h = p_c$.

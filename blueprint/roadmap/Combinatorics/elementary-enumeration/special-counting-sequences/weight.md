# Weight of a southeast path

Let $R$ be a commutative monoid, written multiplicatively, let
$x = (x_j)_{j \in \mathbb{N}}$ be a family of elements of $R$, let $p, q \in \mathbb{N}^2$, and let
$v = [v_0, \dots, v_m]$ be a southeast path from $p$ to $q$. For $1 \le t \le m$, the step from
$v_{t-1}$ to $v_t$ has weight $w_t = x_j$ if it is an east step at height $j$, that is,
$v_{t-1} = (a, j)$ and $v_t = (a+1, j)$, and weight $w_t = 1$ if it is a south step. The weight of
$v$ is $\operatorname{wt}(v) = \prod_{t=1}^{m} w_t$.

For $m = 0$ the product is empty, so the one-point path $[p]$ has weight $1$; so does every path
all of whose steps are south steps. The weight depends only on the list $v$.

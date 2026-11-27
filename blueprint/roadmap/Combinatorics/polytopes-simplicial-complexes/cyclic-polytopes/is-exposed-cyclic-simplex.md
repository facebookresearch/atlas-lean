# Every vertex set of a cyclic simplex spans a face

Let $t_0, \dots, t_d$ be $d + 1$ distinct real numbers, so that
$C_d(d+1) = \operatorname{conv}\{\gamma(t_0), \dots, \gamma(t_d)\} \subset \mathbb{R}^d$ is a
$d$-simplex. For every set $T$ of indices, $\operatorname{conv}\{\gamma(t_i) : i \in T\}$ is a face
of $C_d(d+1)$, and it contains $\gamma(t_j)$ only for $j \in T$.

Proof: the Lagrange interpolation polynomial $q$ of degree at most $d$ with $q(t_i) = 0$ for
$i \in T$ and $q(t_j) = 1$ for $j \notin T$ gives, through the moment curve, a linear functional
that attains its maximum over the vertices exactly at the $\gamma(t_i)$, $i \in T$.

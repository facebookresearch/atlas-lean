# Upper-bound systems are totally dual integral

For every $b \in \mathbb{R}^n$, the system $x \le b$ (with $A$ the identity matrix) is [totally dual integral](is-tdi.md). Its feasible region is the translated orthant $b - \mathbb{R}^n_{\ge 0}$, not a two-sided box $l \le x \le u$. If $c \in \mathbb{Z}^n$ had a negative coordinate $c_j$, then $c^\top (b - t e_j) = c^\top b - t c_j$ would be unbounded as $t \to \infty$; so a bounded integral objective satisfies $c \ge 0$, and $y = c$ is an integral dual solution of value $b^\top c = c^\top b$, attained at $x = b$.

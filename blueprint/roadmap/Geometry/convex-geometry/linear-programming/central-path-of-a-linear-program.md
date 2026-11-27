# Existence and uniqueness of the central path of a linear program

Consider $\min\{c^{\mathsf T}x : Ax = b,\ x \ge 0\}$ with $A$ of full row rank, and suppose there are $x > 0$ with $Ax = b$ and $(y, s)$ with $s > 0$ and $A^{\mathsf T}y + s = c$. Then for every $\nu > 0$ the barrier function $c^{\mathsf T}x - \nu\sum_j\log x_j$ has a unique minimizer $x(\nu)$ on $\{x > 0 : Ax = b\}$, and $(x, y, s) = (x(\nu), y(\nu), s(\nu))$ is the unique solution of $Ax = b$, $A^{\mathsf T}y + s = c$, $x, s > 0$, $x_js_j = \nu$ for all $j$: $s$ is determined as $s_j = \nu/x_j$, and $y$ by full row rank. Complexity bounds for path-following methods are separate statements.

## Sources

- D. P. Williamson et al., *ORIE 6300 Mathematical Programming I*, lecture 22 notes, Cornell University, Theorem 1, <https://people.orie.cornell.edu/dpw/orie6300/Lectures/lec22.pdf>

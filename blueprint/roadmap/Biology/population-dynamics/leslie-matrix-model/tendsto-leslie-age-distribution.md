# Convergence of the age distribution for a primitive Leslie matrix

Let $L$ be the [Leslie matrix](leslie-matrix.md) of $n$ age classes with real fertilities and
survival coefficients, and suppose that $L$ is primitive: its entries are nonnegative and some power
$L^k$ with $k \ge 1$ has all entries positive. Let $r > 0$, and let $v, w \in \mathbb{R}^n$ have
positive entries with $L v = r v$ and $w^\top L = r w^\top$. Then for every nonzero
$x_0 \in \mathbb{R}^n$ with nonnegative entries and every age class $i$,

$$\frac{(L^t x_0)_i}{\sum_j (L^t x_0)_j} \to \frac{v_i}{\sum_j v_j} \qquad (t \to \infty),$$

the strong ergodic theorem in age-distribution form. No diagonalizability of $L$ is assumed.

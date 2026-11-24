# Growth at the Perron rate for a primitive Leslie matrix

Let $L$ be the [Leslie matrix](leslie-matrix.md) of $n$ age classes with real fertilities and
survival coefficients, and suppose that $L$ is primitive: its entries are nonnegative and some power
$L^k$ with $k \ge 1$ has all entries positive. Let $r > 0$, and let $v, w \in \mathbb{R}^n$ have
positive entries with $L v = r v$ and $w^\top L = r w^\top$. Then for every $x_0 \in \mathbb{R}^n$
and every age class $i$,

$$\frac{(L^t x_0)_i}{r^t} \to \frac{w \cdot x_0}{w \cdot v}\, v_i \qquad (t \to \infty),$$

the strong ergodic theorem in growth-rate form. No diagonalizability of $L$ is assumed, and $x_0$
need not be nonnegative.

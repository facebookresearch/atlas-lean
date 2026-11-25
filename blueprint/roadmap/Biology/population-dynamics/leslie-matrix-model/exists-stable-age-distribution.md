# A primitive Leslie matrix has an attracting stable age distribution

Let $n \ge 1$, let $L$ be the [Leslie matrix](leslie-matrix.md) of $n$ age classes with real
fertilities and survival coefficients, and suppose that $L$ is primitive: its entries are
nonnegative and some power $L^k$ with $k \ge 1$ has all entries positive. Then there are a real
$r > 0$ and a vector $v \in \mathbb{R}^n$ with positive entries summing to $1$ such that $L v = r v$
and, for every nonzero $x_0 \in \mathbb{R}^n$ with nonnegative entries and every age class $i$,

$$\frac{(L^t x_0)_i}{\sum_j (L^t x_0)_j} \to v_i \qquad (t \to \infty).$$

The eigenvalue $r$ and the eigenvector $v$ come from the Perron–Frobenius theorem.

# Cover's function-counting theorem

A dichotomy $\{X^+, X^-\}$ of a finite set $X = \{x_1, \dots, x_N\} \subset \mathbb{R}^d$ is homogeneously linearly separable if some $w \in \mathbb{R}^d$ has $w \cdot x > 0$ for $x \in X^+$ and $w \cdot x < 0$ for $x \in X^-$; the set is in general position if every subset of at most $d$ vectors is linearly independent (Cover 1965, Section I). Cover's Function-Counting Theorem (Theorem 1) states that for $N \ge 1$ and $d \ge 1$, $N$ points in general position in $\mathbb{R}^d$ have exactly

$$C(N, d) = 2\sum_{k=0}^{d-1}\binom{N-1}{k}$$

homogeneously linearly separable dichotomies (Eq. (5)). The empty set, whose single dichotomy is vacuously separable, is excluded. The proof is by induction on $N$ and $d$, starting from $C(1, d) = 2$ (Eq. (12)), through the recursion $C(N + 1, d) = C(N, d) + C(N, d - 1)$: a dichotomy of the old points extends to the new point $x_{N+1}$ in both ways exactly when it is separable by a $w$ orthogonal to $x_{N+1}$, which reduces the count to $d - 1$ dimensions. Consequently a uniformly random dichotomy of $N$ points in general position is separable with probability $C(N, d)/2^N$, which equals $1$ for $N \le d$ and, by the symmetry $\binom{2d-1}{k} = \binom{2d-1}{2d-1-k}$, equals $1/2$ at $N = 2d$; the source calls $2d$ the separating capacity of a homogeneous linear threshold function with $d$ degrees of freedom.

## Expansion

1. Definitions: homogeneous linear threshold functions, separable dichotomies and general position.
2. The recursion $C(N + 1, d) = C(N, d) + C(N, d - 1)$ by projection onto the hyperplane orthogonal to the new point.
3. The initial values and the solution of the recursion, giving Eq. (5).
4. The separation probability $C(N, d)/2^N$, its value $1/2$ at $N = 2d$, and its limits as $d \to \infty$: $1$ when $\limsup N/d < 2$ and $0$ when $\liminf N/d > 2$ (the limits following Eq. (24) of the source, for a fixed relative gap from the separating capacity; along $N = 2d - 1$ the probability tends to $1/2$); compare the [perceptron](../../../../ComputerScience/machine-learning/online-learning-and-boosting/perceptron/README.md).

## Sources

- T. M. Cover, Geometrical and statistical properties of systems of linear inequalities with applications in pattern recognition, IEEE Trans. Electron. Comput. EC-14 (1965), 326–334, Theorem 1 and Eq. (5). <https://doi.org/10.1109/pgec.1965.264137>

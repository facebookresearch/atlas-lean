# Bourgain's polynomial ergodic theorem

Let $(X, \mu)$ be a probability space, let
$T : X \to X$ be a measure-preserving map, let $a : \mathbb{N} \to \mathbb{N}$ be an integer
polynomial sequence, and let $f : X \to \mathbb{R}$ be a function in $L^p(\mu)$ for some
$p$ with $1 < p < \infty$. Then there is a function $F : X \to \mathbb{R}$ such that for
$\mu$-almost every $x \in X$ the polynomial ergodic averages
$\frac{1}{n} \sum_{k=0}^{n-1} f(T^{a(k)}(x))$, $n \ge 1$, where $T^{a(k)}$ is the $a(k)$-fold
iterate of $T$, converge to $F(x)$ as $n \to \infty$.

## Sources

- J. Bourgain, *Pointwise ergodic theorems for arithmetic sets*, Publ. Math. IHÉS 69 (1989). Knill, *Some fundamental theorems in mathematics*, §173. Via leanprover/lean-eval@38361be, problem `bourgain_polynomial_ergodic`.

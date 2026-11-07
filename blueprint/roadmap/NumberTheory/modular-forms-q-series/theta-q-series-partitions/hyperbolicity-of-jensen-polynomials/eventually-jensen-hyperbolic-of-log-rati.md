# Hyperbolicity of Jensen polynomials from a log-ratio expansion

Let $\alpha$, $A$ and
$\delta$ be sequences of positive real numbers indexed by $n \in \mathbb{N}$ with
$\delta(n) \to 0$, let $d \ge 1$ be an integer, and for $3 \le j \le d$ let $g_j$ be a real
sequence with $g_j(n) = o(\delta(n)^j)$ as $n \to \infty$. Suppose that for every natural number
$k \le d$,

$$
\log \frac{\alpha(n + k)}{\alpha(n)} = A(n) k - \delta(n)^2 k^2 + \sum_{j=3}^{d} g_j(n) k^j +
o(\delta(n)^d)
$$

as $n \to \infty$. Then for all sufficiently large $n$ the Jensen polynomial
$J_\alpha^{d,n}(X) = \sum_{j=0}^{d} \binom{d}{j} \alpha(n + j) X^j$ is hyperbolic: the number of
its real roots, counted with multiplicity, equals its degree.

The source also proves that suitably renormalized Jensen polynomials converge to the Hermite
polynomials; that conclusion is not part of this statement.

## Sources

- Jashan Bal, Fern Haraldson, Joshua Males and Ian Thompson, *Jensen Polynomials Associated with Wright's Circle Method: Hyperbolicity and Turán Inequalities*, INTEGERS 25 (2025), Article A36, Theorem 5 (`integers-2025-A36-thm-5`), quoted there from Griffin, Ono, Rolen and Zagier.

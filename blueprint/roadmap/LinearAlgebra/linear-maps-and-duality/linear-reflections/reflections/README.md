# Reflections

Let $R$ be a commutative ring and $M$ an $R$-module, let $x \in M$, and let $f \colon M \to R$ be an $R$-linear form with
$f(x) = 2$. The reflection attached to $x$ and $f$ is the linear bijection $s \colon M \to M$,
$s(y) = y - f(y)\, x$, which is its own inverse. This is the general form of the reflection of a Euclidean space $E$,
a finite-dimensional real inner product space, in the hyperplane orthogonal to a nonzero vector $\alpha$: taking
$R = \mathbb R$, $M = E$, $x = \alpha$ and $f(y) = 2\langle y, \alpha\rangle / \langle \alpha, \alpha\rangle$ gives
$\sigma_\alpha(\beta) = \beta - \frac{2\langle \beta, \alpha\rangle}{\langle \alpha, \alpha\rangle}\, \alpha$.

## Idea

The Euclidean reflection $\sigma_\alpha$ fixes the hyperplane orthogonal to $\alpha$ pointwise and sends $\alpha$ to
$-\alpha$. Such reflections generate the Weyl groups of root systems, and in numerical linear algebra they are the
Householder transformations. In general $s$ fixes every vector of $\ker f$ and sends $x$ to $-x$, and the condition
$f(x) = 2$ makes $s \circ s$ the identity, since $s(s(y)) = y + f(y)\,(f(x) - 2)\, x$. Over a ring, $\ker f$ need not
be a hyperplane, nor contain every vector that $s$ fixes: over $\mathbb Z/4\mathbb Z$, with $M = R$, $x = 2$ and $f$ the
identity, $s(y) = -y$ fixes $2$, which is not in $\ker f$.

## Statements

- [Reflection attached to a vector and a linear form](reflection.md)

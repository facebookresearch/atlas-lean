# Möbius algebra product

Let $L$ be a lattice with meet $\wedge$ and let $R$ be a
commutative semiring. The Möbius algebra $A(L, R)$ is the set of functions $f \colon L \to R$ with
$f(s) \neq 0$ for only finitely many $s \in L$. The product of $f, g \in A(L, R)$ is the function
$f \cdot g \in A(L, R)$ given by

$$(f \cdot g)(u) = \sum_{s \wedge t = u} f(s)\, g(t) \qquad (u \in L),$$

the sum taken over all pairs $(s, t) \in L \times L$ with $f(s) \neq 0$, $g(t) \neq 0$ and
$s \wedge t = u$. Equivalently, identifying each $s \in L$ with the function that is $1$ at $s$
and $0$ elsewhere, it is the bilinear extension of $s \cdot t = s \wedge t$.

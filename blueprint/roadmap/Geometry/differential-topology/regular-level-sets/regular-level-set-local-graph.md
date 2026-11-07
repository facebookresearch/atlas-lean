# Regular level sets are locally graphs

Let $f \colon \mathbb{R}^{k+m} \to \mathbb{R}^m$ be a
$C^1$ map and let $x_0 \in \mathbb{R}^{k+m}$ be a point at which the derivative $Df(x_0)$ is
surjective. Then there exist a linear isomorphism
$e \colon \mathbb{R}^{k+m} \to \mathbb{R}^k \times \mathbb{R}^m$, a neighbourhood $U$ in
$\mathbb{R}^k$ of the first component of $e(x_0)$, a map $g \colon \mathbb{R}^k \to \mathbb{R}^m$
that is $C^1$ on $U$, and a neighbourhood $V$ of $x_0$ such that a point $x \in V$ satisfies
$f(x) = f(x_0)$ if and only if $e(x) = (u, g(u))$ for some $u \in U$.

Proof: A projection onto the derivative kernel supplies adapted linear coordinates. The
product-space implicit function theorem then identifies the level set with a local `C¹` graph
(https://en.wikipedia.org/wiki/Implicit_function_theorem).

## Sources

- undergrad.yaml `Submanifolds of R^n / local graphs` (missing); J. Lee, Introduction to Smooth Manifolds, 2nd ed., Ch. 4 (rank theorem).

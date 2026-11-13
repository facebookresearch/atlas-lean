# Laplacian on a vector space as a sum of second directional derivatives

Let $F$ be a
finite-dimensional real inner product space of dimension $n$ with its standard Riemannian
metric, let $f : F \to \mathbb{R}$ and $x \in F$, and let $e_1, \dots, e_n$ be the orthonormal
basis of the tangent space $T_xF$ used in the definition of the Laplacian, viewed as vectors of
$F$. For each $i$ let $g_i(y) = Df(y)(e_i)$, where $D$ denotes the Fréchet derivative. Then the
Laplacian of $f$ at $x$ is $\Delta f(x) = \sum_{i=1}^{n} Dg_i(x)(e_i)$. No differentiability of
$f$ is assumed; a Fréchet derivative that does not exist is taken to be $0$.

When $Df$ is differentiable at $x$, the right side is the flat Laplacian
$\sum_i D^2 f(x)(e_i, e_i)$ of $f$ at $x$.

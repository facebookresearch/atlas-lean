# The Laplacian on a vector space is the flat Laplacian at twice-differentiable points

Let
$F$ be a finite-dimensional real inner product space with its standard Riemannian metric, let
$f : F \to \mathbb{R}$ and $x \in F$, and let $Df$ denote the Fréchet derivative of $f$, taken to
be $0$ at points where $f$ is not differentiable. Suppose $Df$ is differentiable at $x$, with
derivative $D^2 f(x)$ there. Then the Laplacian $\Delta f(x)$ equals $\sum_i D^2 f(x)(b_i, b_i)$
for any orthonormal basis $(b_i)$ of $F$, the flat Laplacian of $f$ at $x$.

Without the hypothesis the two can differ: $D^2 f(x)$ is taken to be $0$ when $Df$ is not
differentiable at $x$, while $\Delta f(x)$ is the sum, over the vectors $v$ of the orthonormal
basis used in its definition, of the derivative at $x$ in direction $v$ of the function
$y \mapsto Df(y)(v)$.

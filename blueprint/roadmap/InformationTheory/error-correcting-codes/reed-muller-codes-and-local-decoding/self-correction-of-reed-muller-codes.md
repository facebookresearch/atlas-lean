# Self-correction of Reed-Muller codes by interpolation along lines

Let $\mathbb{F}$ be a field with distinct nonzero nodes $\nu_0, \dots, \nu_d$, and let $\lambda_0, \dots, \lambda_d$ be the Lagrange weights at $0$, so that $g(0) = \sum_i \lambda_i g(\nu_i)$ for every univariate polynomial $g$ of degree at most $d$. For every polynomial $p$ of total degree at most $d$ on $\mathbb{F}^m$, $p(x) = \sum_i \lambda_i\, p(x + \nu_i v)$ for all $x, v$. For a received word $w$ and the interpolation decoder $x, v \mapsto \sum_i \lambda_i w(x + \nu_i v)$, at every point $x$ at most $(d + 1)\cdot |\{y : w(y) \ne p(y)\}|$ directions $v \in \mathbb{F}^m$ make it err.

## Proof sketch

The restriction $c \mapsto p(x + c v)$ has degree at most $d$, so Lagrange interpolation at the nodes recovers its value at $0$. For a fixed node $\nu_i \ne 0$ the queried point $x + \nu_i v$ ranges bijectively over $\mathbb{F}^m$ as $v$ does, so each corrupted point spoils at most one direction per node.

## Depends on

- [Minimum distance of q-ary Reed-Muller codes](minimum-distance-of-q-ary-reed-muller-codes.md)
- [Lagrange interpolant](../../../Analysis/approximation-theory/lagrange-interpolation/eval-interpolant.md)

## Sources

- S. Arora, B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
- V. Guruswami, A. Rudra, M. Sudan, "Essential Coding Theory", draft book, 2019.

# Self-correction of Reed-Muller codes by interpolation along lines

Let $\mathbb{F}_q$ be a finite field, $d < q - 1$, and $\mathrm{RM}_q(m, d)$ the Reed-Muller code of evaluation tables on $\mathbb{F}_q^m$ of polynomials of total degree at most $d$. Fix a set $S \subseteq \mathbb{F}_q \setminus \{0\}$ of $d + 1$ nodes. Consider the interpolation decoder that, given a received word $w$ and a point $x \in \mathbb{F}_q^m$, picks $v \in \mathbb{F}_q^m$ uniformly at random, queries $w$ at the $d + 1$ points $x + \lambda v$, $\lambda \in S$, and outputs $h(0)$ for the unique univariate polynomial $h$ of degree at most $d$ with $h(\lambda) = w(x + \lambda v)$ for all $\lambda \in S$. If $w$ differs from a codeword $p \in \mathrm{RM}_q(m, d)$ on at most a $\delta$ fraction of the points of $\mathbb{F}_q^m$, then for every $x$ the decoder outputs $p(x)$ with probability at least $1 - (d + 1)\delta$.

## Proof sketch

If all queries go to uncorrupted points, $h$ is the restriction of $p$ to the line $\{x + \lambda v\}$, which has degree at most $d$, so $h(0) = p(x)$. Each individual query $x + \lambda v$ with $\lambda \ne 0$ is uniformly distributed on $\mathbb{F}_q^m$, so by a union bound over the $d + 1$ queries the decoder errs with probability at most $(d + 1)\delta$.

The following forms are derived here and are not stated in the cited sources. With $\lambda_0, \dots, \lambda_d$ the Lagrange weights at $0$ for the nodes $\nu_0, \dots, \nu_d$ of $S$, the decoder outputs $\sum_i \lambda_i w(x + \nu_i v)$, and $p(x) = \sum_i \lambda_i\, p(x + \nu_i v)$ holds for all $x, v$ (over any field with distinct nonzero nodes). Counting instead of averaging: for a fixed node $\nu_i \ne 0$ the point $x + \nu_i v$ ranges bijectively over $\mathbb{F}_q^m$ as $v$ does, so at most $(d + 1)\cdot|\{y : w(y) \ne p(y)\}|$ directions $v \in \mathbb{F}_q^m$ make the decoder err at $x$.

## Depends on

- [Minimum distance of q-ary Reed-Muller codes](minimum-distance-of-q-ary-reed-muller-codes.md)
- [Lagrange interpolant](../../../Analysis/approximation-theory/lagrange-interpolation/eval-interpolant.md)

## Sources

- S. Yekhanin, "Locally Decodable Codes", Foundations and Trends in Theoretical Computer Science 6(3), 2012, Section 2.2.1, Proposition 2.4 and its proof.
- S. Arora, B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
- V. Guruswami, A. Rudra, M. Sudan, "Essential Coding Theory", draft book, 2019.

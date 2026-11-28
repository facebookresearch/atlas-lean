# Local decoding of Reed-Muller codes from punctured lines

Let $\mathbb{F}_q$ be a finite field, $d < q - 1$, and $\mathrm{RM}_q(m, d)$ the Reed-Muller code of evaluation tables on $\mathbb{F}_q^m$ of polynomials of total degree at most $d$. Consider the line decoder that, given a received word $w$ and a point $x \in \mathbb{F}_q^m$, picks $v \in \mathbb{F}_q^m$ uniformly at random, reads $w$ only on the $q - 1$ points $x + \lambda v$ with $\lambda \in \mathbb{F}_q \setminus \{0\}$, and outputs $h(0)$ for the unique univariate polynomial $h$ of degree at most $q - 2$ with $h(\lambda) = w(x + \lambda v)$ for all $\lambda \ne 0$. If $w$ differs from a codeword $f \in \mathrm{RM}_q(m, d)$ on at most a $\delta$ fraction of the points of $\mathbb{F}_q^m$, then for every $x$ the decoder outputs $f(x)$ with probability at least $1 - (q - 1)\delta$.

## Proof sketch

Since $\mathrm{RM}_q(m, d) \subseteq \mathrm{RM}_q(m, q - 2)$, this is the basic line decoder for degree $q - 2$ with query set $S = \mathbb{F}_q \setminus \{0\}$ of size $(q - 2) + 1$. If no query hits a corrupted point, $h$ is the restriction of $f$ to the line $\{x + \lambda v\}$, so $h(0) = f(x)$; each single query $x + \lambda v$ with $\lambda \ne 0$ is uniformly distributed on $\mathbb{F}_q^m$, so a union bound over the $q - 1$ queries bounds the error probability by $(q - 1)\delta$.

The following explicit forms are derived here and are not stated in the cited sources. For a univariate $g$ of degree at most $q - 2$ one has $\sum_{c \in \mathbb{F}_q} g(c) = 0$, because $\sum_{c} c^i = 0$ for $0 \le i < q - 1$; hence $h(0) = -\sum_{\lambda \ne 0} w(x + \lambda v)$, and $\sum_{c \in \mathbb{F}_q} f(x + c v) = 0$ for every codeword, point and direction. Counting instead of averaging: every point other than $x$ lies on the punctured lines of exactly $q - 1$ nonzero directions, so at most $(q - 1)\Delta(w, f)$ of the $q^m - 1$ nonzero directions make the decoder err, where $\Delta$ is Hamming distance.

## Depends on

- [Minimum distance of q-ary Reed-Muller codes](minimum-distance-of-q-ary-reed-muller-codes.md)
- [Lagrange interpolant](../../../Analysis/approximation-theory/lagrange-interpolation/eval-interpolant.md)

## Sources

- S. Yekhanin, "Locally Decodable Codes", Foundations and Trends in Theoretical Computer Science 6(3), 2012, Section 2.2.1, Proposition 2.4 and its proof (applied with $d + 1 = q - 1$).
- S. Arora, B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
- V. Guruswami, A. Rudra, M. Sudan, "Essential Coding Theory", draft book, 2019.

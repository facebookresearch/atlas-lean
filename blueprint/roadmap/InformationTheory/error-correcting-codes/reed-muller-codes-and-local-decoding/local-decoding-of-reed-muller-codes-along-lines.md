# Local decoding of Reed-Muller codes from punctured lines

Let $\mathbb{F}$ have $q$ elements and $d + 1 < q$. For every codeword $f \in \mathrm{RM}_q(m, d)$ and every line, $\sum_{c \in \mathbb{F}} f(x + c v) = 0$, so $f(x) = -\sum_{c \ne 0} f(x + c v)$ for every point $x$ and direction $v \ne 0$. The line decoder reads a received word $w$ only on the $q - 1$ points $x + cv$, $c \ne 0$, and outputs $-\sum_{c \ne 0} w(x + c v)$. For every $x$, at most $(q - 1)\cdot\Delta(w, f)$ of the $q^m - 1$ nonzero directions make it err, where $\Delta$ is Hamming distance; so a uniformly random nonzero direction decodes $f(x)$ correctly with probability at least $1 - (q - 1)\Delta(w, f)/(q^m - 1)$.

## Proof sketch

Restricted to a line, $f$ is a univariate polynomial of degree at most $d < q - 1$, and the values of such a polynomial sum to zero over a finite field. The decoder errs only if the punctured line meets a corrupted point, and every point other than $x$ lies on the punctured lines of exactly $q - 1$ nonzero directions.

## Depends on

- [Minimum distance of q-ary Reed-Muller codes](minimum-distance-of-q-ary-reed-muller-codes.md)

## Sources

- S. Arora, B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
- V. Guruswami, A. Rudra, M. Sudan, "Essential Coding Theory", draft book, 2019.

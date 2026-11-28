# A proper ideal times its conjugate

Let $a, b, c \in \mathbb{Z}$ with $\gcd(a, b, c) = 1$,
$a > 0$ and $b^2 - 4ac < 0$, let $\tau \in \mathbb{C}$ satisfy $a\tau^2 + b\tau + c = 0$, let
$\alpha \in \mathbb{C}$ with $\alpha \neq 0$, and put $\mathcal{O} = \mathbb{Z} + \mathbb{Z}a\tau$.
Let $L$ be a period pair whose lattice is $L = \mathbb{Z}\alpha + \mathbb{Z}\alpha\tau$ and is
contained in $\mathcal{O}$, and let $N = [\mathcal{O} : L]$ be its index (as additive subgroups of
$\mathbb{C}$). Then, as $\mathbb{Z}$-submodules of $\mathbb{C}$, with $\bar{L}$ the image of $L$
under complex conjugation,

$$L\bar{L} = N\mathcal{O}, \qquad N \neq 0, \qquad L \cdot N^{-1}\bar{L} = \mathcal{O}.$$

When $L$ is a proper $\mathcal{O}$-ideal, Sutherland's proof puts it in exactly this form, and the
statement is $\mathfrak{a}\bar{\mathfrak{a}} = (N\mathfrak{a})$ with $N\mathfrak{a} = [\mathcal{O} :
\mathfrak{a}]$, so that $\mathfrak{a}^{-1} = \frac{1}{N\mathfrak{a}}\bar{\mathfrak{a}}$.

## Sources

- Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT OpenCourseWare, Fall 2025, Lecture 17, Theorem 17.10 and its proof, from the point where $\mathfrak{a} = \alpha[1, \tau]$ and $\mathcal{O} = [1, a\tau]$ have been obtained; the product formula `BinaryQuadraticForm.span_mul_map_conj_span` and the index computation `BinaryQuadraticForm.relIndex_span_pair_eq` are written out here.

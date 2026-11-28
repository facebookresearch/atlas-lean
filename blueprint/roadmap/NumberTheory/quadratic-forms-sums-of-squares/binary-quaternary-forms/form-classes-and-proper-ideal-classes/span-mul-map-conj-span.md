# A lattice times its conjugate

Let $a, b, c \in \mathbb{Z}$ with $\gcd(a, b, c) = 1$,
$a > 0$ and $b^2 - 4ac < 0$, let $\tau \in \mathbb{C}$ satisfy $a\tau^2 + b\tau + c = 0$, and let
$\alpha \in \mathbb{C}$. Then, as $\mathbb{Z}$-submodules of $\mathbb{C}$,

$$(\mathbb{Z}\alpha + \mathbb{Z}\alpha\tau) \cdot \overline{(\mathbb{Z}\alpha +
\mathbb{Z}\alpha\tau)} = \frac{|\alpha|^2}{a}\,(\mathbb{Z} + \mathbb{Z}a\tau),$$

where the conjugate lattice is the image under complex conjugation.

## Sources

- Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT OpenCourseWare, Fall 2025, Lecture 17, proof of Theorem 17.10, the computation $\mathfrak{a}\bar{\mathfrak{a}} = N(\alpha)[1, \tau, \bar\tau, \tau\bar\tau] = \frac{N(\alpha)}{a}[a, a\tau, -b, c] = \frac{N(\alpha)}{a}[1, a\tau]$; the generator-by-generator verification, with Bézout coefficients for $\gcd(a, b, c) = 1$, is written out here.

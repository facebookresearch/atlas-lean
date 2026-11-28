# The norm of an integral lattice is its index

Let $a, b, c \in \mathbb{Z}$ with $a > 0$ and
$b^2 - 4ac < 0$, let $\tau \in \mathbb{C}$ satisfy $a\tau^2 + b\tau + c = 0$, and let
$\alpha \in \mathbb{C}$ with $\alpha \neq 0$. If
$\mathfrak{a} = \mathbb{Z}\alpha + \mathbb{Z}\alpha\tau$ is contained in
$\mathcal{O} = \mathbb{Z} + \mathbb{Z}a\tau$, then the index of $\mathfrak{a}$ in $\mathcal{O}$
(as additive subgroups of $\mathbb{C}$) is $[\mathcal{O} : \mathfrak{a}] = |\alpha|^2 / a$, and it
is nonzero.

## Sources

- Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT OpenCourseWare, Fall 2025, Lecture 17, proof of Theorem 17.10, the computation $N(\mathfrak{a}) = [\mathcal{O} : \mathfrak{a}] = N(\alpha)/a$. The argument written out here writes $\alpha = x + y\,a\tau$ and $\alpha\tau = z + w\,a\tau$, computes the index as the determinant $|xw - yz|$, and compares imaginary parts of $\bar\alpha \cdot \alpha\tau = |\alpha|^2\tau$ to get $|\alpha|^2 = a(xw - yz)$.

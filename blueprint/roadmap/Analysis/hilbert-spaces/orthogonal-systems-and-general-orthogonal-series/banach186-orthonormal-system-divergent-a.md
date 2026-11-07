# Banach's Problem 186: a complete orthonormal system with divergent Fourier series

There is a
sequence $(\varphi_i)_{i \ge 0}$ of square-integrable real functions on $[0, 1]$, with respect to
Lebesgue measure, that is orthonormal, $\int_0^1 \varphi_i \varphi_j \, dx = \delta_{ij}$ for
all $i, j$, and complete, in the sense that every square-integrable $g$ on $[0, 1]$ with
$\int_0^1 g \varphi_i \, dx = 0$ for all $i$ vanishes almost everywhere on $[0, 1]$, such that
the following holds: for every continuous $f \colon \mathbb{R} \to \mathbb{R}$ that is not
identically zero on $[0, 1]$, with Fourier coefficients $c_i = \int_0^1 f \varphi_i \, dx$, the
partial sums $\sum_{i < N} c_i \varphi_i(t)$ are unbounded in $N$ for almost every
$t \in [0, 1]$.

The $\varphi_i$ are not assumed continuous: the source imposes continuity only on $f$, and
continuity of the $\varphi_i$ would make the claim false (taking $f = \varphi_0$ would give
Fourier coefficients $\delta_{0i}$ and bounded partial sums).

## Sources

- S. Banach, Problem 186 of the Scottish Book; answered by A. M. Olevskii, "Fourier series with respect to general orthogonal systems" (1975). See the commentary in R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser, 2015).

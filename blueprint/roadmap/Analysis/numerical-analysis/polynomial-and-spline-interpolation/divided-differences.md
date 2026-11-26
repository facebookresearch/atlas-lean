# Divided differences

Let $x_0, \dots, x_n$ be distinct real numbers and $f$ a real function defined at them. For $0 \le j \le n$ let $Q_j$ be the polynomial of degree at most $j$ that interpolates $f$ at $x_0, \dots, x_j$, that is $Q_j(x_i) = f(x_i)$ for $i \le j$; it exists, for instance as the [Lagrange interpolant](../../approximation-theory/lagrange-interpolation/eval-interpolant.md), and is unique, since a nonzero polynomial of degree at most $j$ has at most $j$ zeros. The *$j$-th order divided difference* $f[x_0, \dots, x_j]$ is the coefficient of $x^j$ in $Q_j$. In particular $f[x_0] = f(x_0)$ and $f[x_0, x_1] = \bigl(f(x_1) - f(x_0)\bigr)/(x_1 - x_0)$.

Equivalently, $f[x_0, \dots, x_j]$ is the coefficient $a_j$ in Newton's form $Q_n(x) = a_0 + a_1(x - x_0) + \cdots + a_n (x - x_0)\cdots(x - x_{n-1})$ of the interpolating polynomial.

## Depends on

- [Lagrange interpolant](../../approximation-theory/lagrange-interpolation/eval-interpolant.md)

## Sources

- D. Levy, *Introduction to Numerical Analysis*, lecture notes, Department of Mathematics, University of Maryland, version of 4 January 2021, Section 3.3 (Newton's form), Section 3.5, item 3 and (3.22), and Section 3.6, definition (3.23). <https://www.math.umd.edu/~dlevy/resources/notes.pdf>

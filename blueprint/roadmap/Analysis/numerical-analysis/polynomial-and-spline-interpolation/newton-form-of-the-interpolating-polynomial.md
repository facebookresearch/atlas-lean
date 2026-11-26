# Newton form of the interpolating polynomial

Let $x_0, \dots, x_n$ be distinct real numbers and $f$ a real function defined at them. The polynomial of degree at most $n$ that interpolates $f$ at $x_0, \dots, x_n$ is

$$Q_n(x) = f[x_0] + f[x_0, x_1](x - x_0) + \cdots + f[x_0, \dots, x_n] \prod_{k=0}^{n-1} (x - x_k),$$

in terms of the [divided differences](divided-differences.md) of $f$. Equivalently $Q_j(x) = Q_{j-1}(x) + f[x_0, \dots, x_j] \prod_{k < j} (x - x_k)$ for $1 \le j \le n$, so adding a node adds one term.

## Depends on

- [Divided differences](divided-differences.md)

## Sources

- D. Levy, *Introduction to Numerical Analysis*, lecture notes, Department of Mathematics, University of Maryland, version of 4 January 2021, Section 3.3, the construction (3.3) in the proof of Theorem 3.1, and Section 3.6, formula (3.24). <https://www.math.umd.edu/~dlevy/resources/notes.pdf>

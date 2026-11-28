# Recursion for divided differences

For distinct real numbers $x_0, \dots, x_n$, $n \ge 1$, and a real function $f$ defined at them, the [divided differences](divided-differences.md) satisfy

$$f[x_0, \dots, x_n] = \frac{f[x_1, \dots, x_n] - f[x_0, \dots, x_{n-1}]}{x_n - x_0}.$$

With $f[x_i] = f(x_i)$ this computes all divided differences in a triangular table with $O(n^2)$ operations. The proof shows that $Q_n(x) = P(x) + \frac{x - x_n}{x_n - x_0}\bigl(P(x) - Q_{n-1}(x)\bigr)$, where $P$ interpolates $f$ at $x_1, \dots, x_n$ and $Q_{n-1}$ at $x_0, \dots, x_{n-1}$, and compares the coefficients of $x^n$.

## Depends on

- [Divided differences](divided-differences.md)

## Sources

- D. Levy, *Introduction to Numerical Analysis*, lecture notes, Department of Mathematics, University of Maryland, version of 4 January 2021, Section 3.6, Lemma 3.7 and its proof. <https://www.math.umd.edu/~dlevy/resources/notes.pdf>

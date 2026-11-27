# Explicit formula for divided differences

For distinct real numbers $x_0, \dots, x_n$ and a real function $f$ defined at them, the [divided difference](divided-differences.md) is

$$f[x_0, \dots, x_n] = \sum_{j=0}^{n} \frac{f(x_j)}{\prod_{k \ne j} (x_j - x_k)}.$$

In particular it is a symmetric function of $x_0, \dots, x_n$: it does not depend on the order of the points. It is the [coefficient formula of Lagrange interpolation](coefficient-of-a-polynomial-from-its-values.md), proved in Mathlib for every field, applied to the interpolating polynomial $Q$ of $f$ at the nodes: by definition the divided difference is the coefficient of $x^n$ in $Q$, $\deg Q \le n$, and $Q(x_j) = f(x_j)$, also when $\deg Q < n$.

## Depends on

- [Divided differences](divided-differences.md)

## Proof depends on

- [Lagrange interpolant](../../approximation-theory/lagrange-interpolation/eval-interpolant.md)
- [Coefficient of index m − 1 of a polynomial of degree below m from its values at m distinct nodes](coefficient-of-a-polynomial-from-its-values.md)

## Sources

- D. Levy, *Introduction to Numerical Analysis*, lecture notes, Department of Mathematics, University of Maryland, version of 4 January 2021, Section 3.5, item 3 and formula (3.22), and the remark in Section 3.7 that the order of the points does not change the divided difference. <https://www.math.umd.edu/~dlevy/resources/notes.pdf>

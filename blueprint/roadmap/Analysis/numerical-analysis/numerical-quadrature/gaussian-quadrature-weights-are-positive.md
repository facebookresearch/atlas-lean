# The weights of Gaussian quadrature are positive

The weights $A_0, \dots, A_n$ of the [Gaussian quadrature](gaussian-quadrature.md) with $n + 1$ nodes for a weight $w$ on $[a, b]$ are positive, and their sum is $\int_a^b w(x)\, dx$.

For a fixed $j$, the polynomial $p(x) = q(x)/(x - x_j)$ has degree $n$, so the rule is exact for $p^2$, and $0 < \int_a^b p^2 w = \sum_i A_i p(x_i)^2 = A_j p(x_j)^2$; exactness for $f \equiv 1$ gives the sum.

## Depends on

- [Gaussian quadrature](gaussian-quadrature.md)

## Proof depends on

- [Gaussian quadrature is exact to degree 2n + 1](gaussian-quadrature-is-exact-to-degree-2n-plus-1.md)

## Sources

- D. Levy, *Introduction to Numerical Analysis*, lecture notes, Department of Mathematics, University of Maryland, version of 4 January 2021, Section 6.7.2, Lemma 6.11 and its proof. <https://www.math.umd.edu/~dlevy/resources/notes.pdf>

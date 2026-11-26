# Gaussian quadrature is exact to degree 2n + 1

The [Gaussian quadrature](gaussian-quadrature.md) with $n + 1$ nodes for a weight $w$ on $[a, b]$ is exact for every polynomial of degree at most $2n + 1$:

$$\int_a^b f(x)\, w(x)\, dx = \sum_{i=0}^{n} A_i f(x_i) \qquad (\deg f \le 2n + 1).$$

Dividing $f$ by the orthogonal polynomial $q$ whose zeros are the nodes gives $f = qp + r$ with $\deg p, \deg r \le n$; the term $qp$ integrates to $0$ against $w$ and vanishes at the nodes, and the rule is exact for $r$. For example, the two-point rule $\int_{-1}^{1} f(x)\, dx \approx f(-1/\sqrt{3}) + f(1/\sqrt{3})$, whose nodes are the zeros of the Legendre polynomial $P_2$, is exact for cubic polynomials.

## Depends on

- [Gaussian quadrature](gaussian-quadrature.md)

## Proof depends on

- [Interpolatory quadrature rules](interpolatory-quadrature.md)

## Sources

- D. Levy, *Introduction to Numerical Analysis*, lecture notes, Department of Mathematics, University of Maryland, version of 4 January 2021, Section 6.7.1, Theorem 6.7 and its proof, and Examples 6.6, 6.9 and 6.10. <https://www.math.umd.edu/~dlevy/resources/notes.pdf>

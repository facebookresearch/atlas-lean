# Copositivity has polynomial-size integer certificates of failure

A symmetric matrix $M$ is *copositive* if $x^{T}Mx\ge0$ for all entrywise nonnegative $x$. If a rational symmetric matrix $M$ is not copositive, then there is a nonnegative integer vector $x$ with $x^{T}Mx<0$ whose entries have bit length polynomial in the bit length of $M$. Hence non-copositivity is in $\mathsf{NP}$ (copositivity is in $\mathsf{coNP}$).

## Proof sketch

Minimize $x^{T}Mx$ over the standard simplex; at a minimizer with negative value, the KKT conditions make $Mx^\ast$ constant and negative on the support of $x^\ast$, so $x^\ast$ lies in the polyhedron $\{(x_S, \lambda') : M_{SS}x_S=\lambda'\mathbb{1},\ \mathbb{1}^{T}x_S = 1,\ x_S \ge 0,\ \lambda' \le \lambda\}$ with $\lambda < 0$. Any point of it has $x^{T}Mx = \lambda' < 0$, and a vertex has rational coordinates of polynomial bit length (Cramer's rule); clearing denominators gives the integer certificate.

## Depends on

- [The complexity class NP](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/np.md)

## Proof depends on

- [Small integer solutions of linear systems (Siegel-type bounds)](small-integer-solutions-of-linear-systems.md)

## Sources

- Katta G. Murty, Santosh N. Kabadi, "Some NP-Complete Problems in Quadratic and Nonlinear Programming", Mathematical Programming 39(2), 1987.
- Alexander Schrijver, "Theory of Linear and Integer Programming", John Wiley & Sons, 1986.

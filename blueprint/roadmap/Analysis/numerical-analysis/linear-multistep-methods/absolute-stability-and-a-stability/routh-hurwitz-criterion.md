# Routh–Hurwitz criterion

Let $q(z) = a_0 z^k + a_1 z^{k-1} + \dots + a_k$ be a polynomial with real coefficients and $a_0 > 0$, and let $Q$ be the $k \times k$ matrix whose $(i, j)$ entry is $a_{2j - i}$, with $a_m = 0$ for $m < 0$ or $m > k$:

$$Q = \begin{pmatrix} a_1 & a_3 & a_5 & \cdots & a_{2k-1} \\ a_0 & a_2 & a_4 & \cdots & a_{2k-2} \\ 0 & a_1 & a_3 & \cdots & a_{2k-3} \\ 0 & a_0 & a_2 & \cdots & a_{2k-4} \\ \vdots & & & & \vdots \end{pmatrix}.$$

Then every root of $q$ lies in the open left half-plane $\Re z < 0$ if and only if all leading principal minors of $Q$ are positive.

Under the map $z = (r - 1)/(r + 1)$, which takes the open unit disc onto the open left half-plane, $(1 - z)^k \pi\big(\tfrac{1+z}{1-z}; \bar h\big)$ is such a polynomial for real $\bar h$, so the criterion decides absolute stability of a linear multistep method.

## Related topics

- [Schur's criterion](schur-criterion.md)
- [Routh–Hurwitz criterion for cubic polynomials](../../../control-theory/feedback-stability-and-classical-design/routh-hurwitz-criterion-for-cubic-polynomials.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 3.7.2, the transformation to (81) and Theorem 15 (Routh–Hurwitz criterion, stated without proof there), with the matrix $Q$. <https://people.maths.ox.ac.uk/suli/nsodes.pdf>

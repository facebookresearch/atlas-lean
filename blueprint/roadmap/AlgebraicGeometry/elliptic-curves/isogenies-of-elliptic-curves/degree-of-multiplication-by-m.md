# Multiplication by m has degree m squared

For a nonzero integer $m$, multiplication by $m$ on an elliptic curve is an isogeny of degree $m^2$. It is separable exactly when $m$ is not divisible by the characteristic.

Let $E$ be an elliptic curve over a field $k$ and $m$ a nonzero integer. Then the [isogeny](isogeny-of-elliptic-curves.md) $[m]\colon E\to E$, $P\mapsto mP$, is nonzero and

$$
\deg[m]=m^2 .
$$

It is separable if and only if $\operatorname{char}k$ does not divide $m$; in characteristic $0$ it is always separable. For $m=0$ the map $[0]$ is the zero isogeny, of degree $0=0^2$.

## Depends on

- [Isogeny of elliptic curves](isogeny-of-elliptic-curves.md)

## Proof depends on

- [The kernel of an isogeny has order its separable degree](kernel-order-equals-separable-degree.md)

## Expansion

For a curve $y^2=x^3+Ax+B$ (characteristic not $2$ or $3$), Sutherland writes $[n]$ for $n>0$ in terms of the division polynomials as $(\phi_n/\psi_n^2,\ \omega_n/\psi_n^3)$ and shows that $\phi_n$ has degree $n^2$, that $\psi_n^2$ has smaller degree and that the two are coprime, so $\deg[n]=n^2$; $[-n]=[-1]\circ[n]$ has the same degree. The leading term $n^2x^{n^2-1}$ of $\phi_n'$ is nonzero exactly when the characteristic does not divide $n$, which gives separability; when it divides $n$, the kernel of $[n]$ has fewer than $n^2$ points, so $[n]$ is inseparable by the kernel count. For general Weierstrass models, Galbraith gets the degree from the dual isogeny and separability from the invariant differential, $[m]^*\omega=m\,\omega$. A good expansion adds pages for the degree and coprimality facts about division polynomials, and for the standard form of an isogeny.

## Sources

- Andrew V. Sutherland, *18.783 Elliptic Curves*, MIT lecture notes, Spring 2021, [Lecture 5: Isogeny kernels and division polynomials](https://math.mit.edu/classes/18.783/2021/LectureNotes5.pdf), Theorem 5.25.
- Steven D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press (2012); extended and corrected version 2.0 of Chapter 9, [author's copy](https://www.math.auckland.ac.nz/~sgal018/crypto-book/ch9.pdf) (numbering of the extended version), Corollary 9.6.28 and Corollary 9.7.3.
- Denis X. Charles, Eyal Z. Goren, Kristin E. Lauter, "Cryptographic Hash Functions from Expander Graphs", *Journal of Cryptology* 22 (2009) 93–113, [doi:10.1007/s00145-007-9002-x](https://doi.org/10.1007/s00145-007-9002-x), Section 2.2.

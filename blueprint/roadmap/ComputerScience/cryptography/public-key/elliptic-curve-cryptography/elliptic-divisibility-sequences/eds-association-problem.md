# EDS association problem

Given points $P$ and $Q=[k]P\ne O$ on an elliptic curve over a finite field, with $k$ the minimal multiplier and $\operatorname{ord}(P)\ge4$, the EDS association problem asks for $W_{E,P}(k)=\psi_k(P)$, the value at $P$ of the $k$-th division polynomial, without being given $k$.

Let $E$ be an elliptic curve over a finite field $K$ given by a Weierstrass equation, and let $P,Q\in E(K)$ with $P$ affine, $Q\in\langle P\rangle$, $Q\ne O$ and $\operatorname{ord}(P)\ge4$. Here $\psi_n$ ($n\in\mathbb{Z}$) are the integer-indexed division polynomials of the Weierstrass equation of $E$, and $W_{E,P}(n)=\psi_n(x_P,y_P)$ for $P=(x_P,y_P)$ is the elliptic divisibility sequence of $P$; $W_{E,P}(n)=0$ exactly when $[n]P=O$. The *minimal multiplier* of $Q\in\langle P\rangle$ with respect to $P$ is the least integer $k\ge0$ with $Q=[k]P$. Let $k$ be the minimal multiplier of $Q$ with respect to $P$, so $0<k<\operatorname{ord}(P)$. The *EDS association problem* is: given $E$, $P$ and $Q$, determine

$$
W_{E,P}(k)=\psi_k(x_P,y_P)\in K .
$$

## Depends on

- [Elliptic-curve discrete logarithm problem](../elliptic-curve-discrete-logarithm-problem.md)
- [Torsion Cardinality](../../../../../AlgebraicGeometry/not-yet-classified/smul-some-eq-zero-iff.md)

## Proof depends on

None.

## Expansion

The sequence is the one given by the division polynomials of the fixed Weierstrass equation, not a rescaling of it. Given $k$, the term $W_{E,P}(k)$ is computable with $O(\log k)$ operations in $K$ by a double-and-add recurrence on blocks of consecutive terms (Lauter and Stange, Theorem 7, after Shipsey), so an ECDLP solver yields a solver for this problem. Prerequisite still to add to this graph: a page for the integer-indexed division polynomials $\psi_n$ of a Weierstrass curve.

## Sources

- K. E. Lauter and K. E. Stange, "The elliptic curve discrete logarithm problem and equivalent hard problems for elliptic divisibility sequences", *Selected Areas in Cryptography (SAC 2008)*, LNCS 5381, Springer, 2009, doi:10.1007/978-3-642-04159-4_20; numbering from arXiv:0803.0728v2, Section 1, Problem 2, Definition 6 and Theorem 7.

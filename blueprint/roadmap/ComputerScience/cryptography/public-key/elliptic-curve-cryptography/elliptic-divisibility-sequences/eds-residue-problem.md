# EDS residue problem

Given points $P$ and $Q=[k]P\ne O$ on an elliptic curve over a finite field of odd characteristic, with $k$ the minimal multiplier and $\operatorname{ord}(P)\ge4$, the EDS residue problem asks whether $W_{E,P}(k)=\psi_k(P)$ is a square in $K^\times$.

Let $E$ be an elliptic curve over a finite field $K$ of characteristic different from $2$ given by a Weierstrass equation, and let $P,Q\in E(K)$ with $P$ affine, $Q\in\langle P\rangle$, $Q\ne O$ and $\operatorname{ord}(P)\ge4$. Here $\psi_n$ ($n\in\mathbb{Z}$) are the division polynomials of the Weierstrass equation of $E$, normalized by $\psi_0=0$, $\psi_1=1$ and $\psi_{-n}=-\psi_n$, and $W_{E,P}(n)=\psi_n(x_P,y_P)$ for $P=(x_P,y_P)$ is the elliptic divisibility sequence of $P$; $W_{E,P}(n)=0$ exactly when $[n]P=O$. The *minimal multiplier* of $Q\in\langle P\rangle$ with respect to $P$ is the least integer $k\ge0$ with $Q=[k]P$. Let $k$ be the minimal multiplier of $Q$ with respect to $P$, so $0<k<\operatorname{ord}(P)$ and $W_{E,P}(k)\ne0$. The *EDS residue problem* is: given $E$, $P$ and $Q$, decide whether

$$
W_{E,P}(k)\in(K^\times)^2 .
$$

## Depends on

None.

## Proof depends on

None.

## Expansion

In characteristic $2$ every element of $K^\times$ is a square, so the question is trivial there. The answer is a single bit about $k$; Lauter and Stange relate it to the ECDLP for points of odd order under further conditions on $P$. Prerequisites still to add to this graph: the division polynomials $\psi_n$ of a Weierstrass curve with their normalization and Ward recurrence, and the criterion that $\psi_n$ vanishes at a nonsingular affine point $P$ exactly when $[n]P=O$.

## Sources

- K. E. Lauter and K. E. Stange, "The elliptic curve discrete logarithm problem and equivalent hard problems for elliptic divisibility sequences", *Selected Areas in Cryptography (SAC 2008)*, LNCS 5381, Springer, 2009, doi:10.1007/978-3-642-04159-4_20; numbering from arXiv:0803.0728v2, Section 1, Problem 3, Definition 6 and Section 7.

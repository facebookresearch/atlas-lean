# Every finite subgroup is the kernel of a separable isogeny

For every finite subgroup $G$ of an elliptic curve there is a separable isogeny with kernel exactly $G$, unique up to an isomorphism of the target. Its target is written $E/G$.

Let $E$ be an elliptic curve over a field $k$ and let $G\subseteq E(\bar k)$ be a finite subgroup. Then:

1. (Geometric existence.) There are an elliptic curve $E'$ and a separable [isogeny](isogeny-of-elliptic-curves.md) $\varphi\colon E\to E'$, both defined over $\bar k$, with $\ker\varphi=G$; its degree is $\#G$.
2. (Uniqueness.) If $\psi\colon E\to E''$ is another separable isogeny over $\bar k$ with $\ker\psi=G$, there is a unique isomorphism $\iota\colon E'\to E''$ over $\bar k$ with $\psi=\iota\circ\varphi$.
3. (Descent.) If $k$ is perfect and $\sigma(G)=G$ for every $\sigma\in\operatorname{Gal}(\bar k/k)$, then $E'$ and $\varphi$ may be taken to be defined over $k$.

The curve $E'$, well defined up to isomorphism, is written $E/G$. The isogeny $\varphi$ itself is not unique: $-\varphi=[-1]\circ\varphi$ has the same kernel, and more generally $\iota\circ\varphi$ does for every automorphism $\iota$ of $E'$.

## Depends on

- [Isogeny of elliptic curves](isogeny-of-elliptic-curves.md)

## Proof depends on

- [The kernel of an isogeny has order its separable degree](kernel-order-equals-separable-degree.md)

## Expansion

The translations $\tau_P\colon Q\mapsto Q+P$ for $P\in G$ form a finite group of automorphisms of the curve $E$, and the quotient curve $E/G$ comes from the fixed field $\bar k(E)^G$. The quotient map is separable and unramified, so by the Hurwitz genus formula $E/G$ has genus $1$; with the image of $O$ as origin it is an elliptic curve, and the quotient map is an isogeny with kernel the orbit of $O$, namely $G$. Its degree is $\#G$ by the kernel count. For uniqueness, a separable $\psi$ with kernel $G$ has $\psi^*\bar k(E'')$ inside $\bar k(E)^G$ of the same index $\#G$, so the two fields agree; $\iota$ is unique because $\varphi$ is surjective. Vélu's formulas give an explicit construction, which also proves item 3. A good expansion adds pages for the quotient of a curve by a finite group of automorphisms and for the Hurwitz genus formula.

Item 2 follows Sutherland, Theorem 5.11, which states uniqueness up to an isomorphism of the target. Galbraith, Theorem 9.6.19, gives existence and says the isogeny is not necessarily unique, and his Exercise 9.6.20 discusses how non-uniqueness arises; De Feo, Proposition 25, states uniqueness without the qualification.

## Sources

- Andrew V. Sutherland, *18.783 Elliptic Curves*, MIT lecture notes, Spring 2021, [Lecture 5: Isogeny kernels and division polynomials](https://math.mit.edu/classes/18.783/2021/LectureNotes5.pdf), Theorem 5.11 and its proof sketch (items 1–3).
- Steven D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press (2012); extended and corrected version 2.0 of Chapter 9, [author's copy](https://www.math.auckland.ac.nz/~sgal018/crypto-book/ch9.pdf) (numbering of the extended version), Theorem 9.6.19 (existence) and Exercise 9.6.20.
- Steven D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press (2012); extended and corrected version 2.0 of Chapter 25, [author's copy](https://www.math.auckland.ac.nz/~sgal018/crypto-book/ch25.pdf) (numbering of the extended version), Section 25.1 and Corollary 25.1.7.
- Luca De Feo, "Mathematics of Isogeny Based Cryptography", lecture notes, arXiv:1711.04062v1 (2017), Proposition 25.

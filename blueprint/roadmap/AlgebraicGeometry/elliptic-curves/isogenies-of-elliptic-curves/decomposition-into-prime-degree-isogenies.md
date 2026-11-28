# A separable isogeny is a composite of prime-degree isogenies

Over an algebraically closed field, a nonzero separable isogeny is, up to an isomorphism of the target, a composite of separable isogenies of prime degree.

Let $\varphi\colon E\to E'$ be a nonzero separable [isogeny](isogeny-of-elliptic-curves.md) of elliptic curves over an algebraically closed field $k$. Then there are elliptic curves $E_0=E,E_1,\dots,E_r$ over $k$, separable isogenies $\varphi_i\colon E_{i-1}\to E_i$ of prime degrees, and an isomorphism $\iota\colon E_r\to E'$, such that

$$
\varphi=\iota\circ\varphi_r\circ\cdots\circ\varphi_1,\qquad \deg\varphi=\prod_{i=1}^{r}\deg\varphi_i .
$$

Here $r$ is the number of prime factors of $\deg\varphi$ counted with multiplicity; when $\deg\varphi=1$, $r=0$ and $\varphi=\iota$ is an isomorphism.

## Depends on

- [Isogeny of elliptic curves](isogeny-of-elliptic-curves.md)

## Proof depends on

- [Every finite subgroup is the kernel of a separable isogeny](separable-isogeny-with-prescribed-kernel.md)
- [An isogeny factors through a separable isogeny with contained kernel](factorization-through-a-separable-isogeny.md)
- [Degrees of isogenies multiply under composition](degree-is-multiplicative.md)
- [First isomorphism theorem for groups](../../../GroupTheory/group-basics/first-isomorphism-groups.md)

## Expansion

Induction on $\deg\varphi$. If $\deg\varphi=1$, $\varphi$ is separable with trivial kernel, hence an isomorphism. Otherwise $G=\ker\varphi$ is a nontrivial finite abelian group, of order $\deg\varphi$, and contains a subgroup $H$ of prime order. Take the separable isogeny $\varphi_1\colon E\to E_1$ with kernel $H$; since $H\subseteq G$, $\varphi=\varphi'\circ\varphi_1$ for an isogeny $\varphi'\colon E_1\to E'$, separable because $\varphi$ is, with kernel $\varphi_1(G)\cong G/H$ (the first isomorphism theorem for $\varphi_1|_G$, whose kernel is $H$) of smaller order; apply the induction hypothesis to $\varphi'$. The degree formula is multiplicativity. Sutherland states this as Corollary 5.12 (together with Frobenius factors for inseparable isogenies). Galbraith's Theorem 25.1.2 gives a version over the ground field, with factors defined over $k$ after a multiplication map is split off; it is not stated here.

## Sources

- Andrew V. Sutherland, *18.783 Elliptic Curves*, MIT lecture notes, Spring 2021, [Lecture 5: Isogeny kernels and division polynomials](https://math.mit.edu/classes/18.783/2021/LectureNotes5.pdf), Theorem 5.11 and Corollary 5.12.
- Steven D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press (2012); extended and corrected version 2.0 of Chapter 25, [author's copy](https://www.math.auckland.ac.nz/~sgal018/crypto-book/ch25.pdf) (numbering of the extended version), Theorem 25.1.2 and its proof.

# Isogeny of elliptic curves

An isogeny of elliptic curves is a morphism of curves that sends the origin to the origin. Its degree is the degree of the extension of function fields it induces, and the zero isogeny has degree $0$.

Let $k$ be a field with algebraic closure $\bar k$, and let $E_1$, $E_2$ be elliptic curves over $k$ with origins $O_1$, $O_2$. An *isogeny* $\varphi\colon E_1\to E_2$ over $k$ is a morphism of curves defined over $k$ with $\varphi(O_1)=O_2$. The constant map with value $O_2$ is the *zero isogeny*.

A nonzero isogeny is nonconstant and induces an injection $\varphi^*\colon\bar k(E_2)\to\bar k(E_1)$ of function fields. Its *degree* is

$$
\deg\varphi=[\bar k(E_1):\varphi^*\bar k(E_2)],
$$

a positive integer, and the zero isogeny has degree $0$. A nonzero isogeny is *separable*, *inseparable* or *purely inseparable* according as this finite extension is. The *kernel* of $\varphi$ is $\ker\varphi=\{P\in E_1(\bar k):\varphi(P)=O_2\}$. The curves are *isogenous* if there is a nonzero isogeny $E_1\to E_2$, and *$d$-isogenous* if there is one of degree $d$; an isogeny of degree $d$ is also called a *$d$-isogeny*.

Conventions. This page counts the zero map as an isogeny, as Galbraith does; Voight, Sutherland and De Feo call only nonconstant maps isogenies, so statements about isogenies elsewhere in this folder say *nonzero* where it matters. An isogeny over $k$ is in particular an isogeny over $\bar k$, and degree and kernel are computed over $\bar k$.

Two facts the sources record with the definition, and which the other pages of this folder use: a nonzero isogeny is surjective on $\bar k$-points, and every isogeny is a homomorphism of the groups of points, so $\ker\varphi$ is a subgroup of $E_1(\bar k)$ and the multiplication-by-$m$ map $[m]$ is an isogeny $E\to E$ for every integer $m$.

## Depends on

None.

## Proof depends on

None.

## Expansion

A definition, but one stated in vocabulary that has no pages yet: morphisms of pointed elliptic curves, viewed as smooth projective curves (rather than Weierstrass coefficients and point maps), the injection of function fields $\varphi^*$ that a nonconstant morphism induces, and the finiteness and separability of that extension. The two recorded facts need their own proofs: surjectivity holds because a nonconstant morphism of smooth projective curves is surjective, and the homomorphism property comes from identifying $E(\bar k)$ with the degree-zero Picard group, on which $\varphi$ acts by push-forward of divisors. A good expansion adds pages for morphisms of curves and their function-field degree, for surjectivity of nonconstant morphisms, and for the homomorphism property.

## Sources

- Steven D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press (2012); extended and corrected version 2.0 of Chapter 9, [author's copy](https://www.math.auckland.ac.nz/~sgal018/crypto-book/ch9.pdf) (numbering of the extended version), Definition 9.6.1, Theorem 9.6.3 and the opening paragraph of Section 9.6.
- Luca De Feo, "Mathematics of Isogeny Based Cryptography", lecture notes, arXiv:1711.04062v1 (2017), Definition 24.
- John Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer (2021), [doi:10.1007/978-3-030-56694-4](https://doi.org/10.1007/978-3-030-56694-4); numbers from the author's corrected edition v.1.0.7u, [author's copy](https://jvoight.github.io/quat-book.pdf), Definition 42.1.2.
- Andrew V. Sutherland, *18.783 Elliptic Curves*, MIT lecture notes, Spring 2021, [Lecture 5: Isogeny kernels and division polynomials](https://math.mit.edu/classes/18.783/2021/LectureNotes5.pdf), opening paragraph.

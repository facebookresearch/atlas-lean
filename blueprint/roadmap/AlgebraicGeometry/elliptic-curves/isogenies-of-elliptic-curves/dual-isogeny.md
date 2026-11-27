# Existence and uniqueness of the dual isogeny

Every nonzero isogeny $\varphi$ of degree $m$ has a unique dual isogeny $\hat\varphi$ in the opposite direction with $\hat\varphi\circ\varphi=[m]$; it also satisfies $\varphi\circ\hat\varphi=[m]$ and has degree $m$.

Let $\varphi\colon E\to E'$ be a nonzero [isogeny](isogeny-of-elliptic-curves.md) of elliptic curves over a field $k$, of degree $m$. Then there is a unique isogeny $\hat\varphi\colon E'\to E$ with

$$
\hat\varphi\circ\varphi=[m]_E .
$$

Moreover $\varphi\circ\hat\varphi=[m]_{E'}$, $\deg\hat\varphi=m$, and $\hat\varphi$ is defined over $k$ when $\varphi$ is. The isogeny $\hat\varphi$ is the *dual* of $\varphi$; by convention the dual of the zero isogeny is zero.

## Depends on

- [Isogeny of elliptic curves](isogeny-of-elliptic-curves.md)

## Proof depends on

- [Every isogeny is a separable isogeny after a power of Frobenius](frobenius-factorization-of-an-isogeny.md)
- [Degrees of isogenies multiply under composition](degree-is-multiplicative.md)
- [Multiplication by m has degree m squared](degree-of-multiplication-by-m.md)
- [A separable isogeny is a composite of prime-degree isogenies](decomposition-into-prime-degree-isogenies.md)
- [An isogeny factors through a separable isogeny with smaller kernel](factorization-through-a-separable-isogeny.md)

## Expansion

Uniqueness: if $\psi_1\circ\varphi=\psi_2\circ\varphi$ then $\psi_1=\psi_2$, because $\varphi$ is surjective. Existence, by induction on the number of prime factors of $m$: write $\varphi$ as a separable isogeny after a power of Frobenius and the separable part as a composite of prime-degree isogenies up to an isomorphism, and dualize each factor. A separable factor $\varphi_i$ of prime degree $\ell$ has kernel inside $E[\ell]=\ker[\ell]$, so if $\ell$ is prime to the characteristic $[\ell]$ is separable and factors as $\hat\varphi_i\circ\varphi_i$. Sutherland's proof of Theorem 6.7 handles the prime-degree step in his own way, separating the separable and the purely inseparable cases (including the Frobenius, through the fact that $[p]$ factors through it); this page does not claim his exact route. Then $\varphi\circ\hat\varphi\circ\varphi=\varphi\circ[m]=[m]\circ\varphi$, and cancelling the surjective $\varphi$ on the right gives $\varphi\circ\hat\varphi=[m]$. The degree follows from $\deg[m]=m^2$ and multiplicativity. Galbraith instead defines $\hat\varphi$ through the pull-back of divisor classes on $\operatorname{Pic}^0$. A good expansion states on its own page that $[p]$ factors through the $p$-power Frobenius, which the purely inseparable case uses.

## Sources

- Andrew V. Sutherland, *18.783 Elliptic Curves*, MIT lecture notes, Spring 2021, [Lecture 6: Torsion subgroups and endomorphism rings](https://math.mit.edu/classes/18.783/2021/LectureNotes6.pdf), Theorem 6.7, Definition 6.8 and Lemma 6.10.
- Steven D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press (2012); extended and corrected version 2.0 of Chapter 9, [author's copy](https://www.math.auckland.ac.nz/~sgal018/crypto-book/ch9.pdf) (numbering of the extended version), Theorem 9.6.21, Exercise 9.6.22, Definition 9.6.23 and Theorem 9.6.27, item 1.
- Luca De Feo, "Mathematics of Isogeny Based Cryptography", lecture notes, arXiv:1711.04062v1 (2017), Theorem 26.
- Anamaria Costache, Brooke Feigon, Kristin Lauter, Maike Massierer, Anna Puskás, "Ramanujan graphs in cryptography", in *Research Directions in Number Theory (Women in Numbers IV)*, Association for Women in Mathematics Series 19, Springer (2019) 1–40, [doi:10.1007/978-3-030-19478-9_1](https://doi.org/10.1007/978-3-030-19478-9_1); numbers from arXiv:1806.05709v2, Theorem 2.2.
- John Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer (2021), [doi:10.1007/978-3-030-56694-4](https://doi.org/10.1007/978-3-030-56694-4); numbers from the author's corrected edition v.1.0.7u, [author's copy](https://jvoight.github.io/quat-book.pdf), paragraph 42.1.3.

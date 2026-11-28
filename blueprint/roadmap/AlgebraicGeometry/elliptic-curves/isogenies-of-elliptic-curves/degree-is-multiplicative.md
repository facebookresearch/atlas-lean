# Degrees of isogenies multiply under composition

The degree, the separable degree and the inseparable degree of a composite of nonzero isogenies are the products of those of the factors.

Let $\gamma\colon E_1\to E_2$ and $\beta\colon E_2\to E_3$ be nonzero [isogenies](isogeny-of-elliptic-curves.md) of elliptic curves over a field $k$, and $\alpha=\beta\circ\gamma$. Then $\alpha$ is a nonzero isogeny and

$$
\deg\alpha=\deg\beta\,\deg\gamma,\qquad \deg_s\alpha=\deg_s\beta\,\deg_s\gamma,\qquad \deg_i\alpha=\deg_i\beta\,\deg_i\gamma .
$$

If one factor is the zero isogeny, the composite is zero and the first formula holds with the convention $\deg 0=0$.

## Depends on

- [Isogeny of elliptic curves](isogeny-of-elliptic-curves.md)
- [In positive characteristic, every nonzero isogeny is a separable isogeny after a power of Frobenius](frobenius-factorization-of-an-isogeny.md)

## Proof depends on

- [The kernel of a nonzero isogeny has order its separable degree](kernel-order-equals-separable-degree.md)

## Expansion

The composite is nonconstant because both factors are surjective on $\bar k$-points. The degree formula is the tower law for $\bar k(E_1)\supseteq\gamma^*\bar k(E_2)\supseteq\gamma^*\beta^*\bar k(E_3)$. For separable degrees, $\ker\alpha=\gamma^{-1}(\ker\beta)$ is a union of $\#\ker\beta$ cosets of $\ker\gamma$, since $\gamma$ is surjective, so $\#\ker\alpha=\#\ker\beta\,\#\ker\gamma$, and kernel orders are separable degrees. The inseparable degrees then multiply because $\deg=\deg_s\deg_i$.

## Sources

- Andrew V. Sutherland, *18.783 Elliptic Curves*, MIT lecture notes, Spring 2021, [Lecture 5: Isogeny kernels and division polynomials](https://math.mit.edu/classes/18.783/2021/LectureNotes5.pdf), Corollary 5.10.
- Steven D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press (2012); extended and corrected version 2.0 of Chapter 9, [author's copy](https://www.math.auckland.ac.nz/~sgal018/crypto-book/ch9.pdf) (numbering of the extended version), Section 9.6, the paragraph after Lemma 9.6.6.
- Anamaria Costache, Brooke Feigon, Kristin Lauter, Maike Massierer, Anna Puskás, "Ramanujan graphs in cryptography", in *Research Directions in Number Theory (Women in Numbers IV)*, Association for Women in Mathematics Series 19, Springer (2019) 1–40, [doi:10.1007/978-3-030-19478-9_1](https://doi.org/10.1007/978-3-030-19478-9_1); numbers from arXiv:1806.05709v2, Section 2.

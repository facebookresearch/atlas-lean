# The kernel of a nonzero isogeny has order its separable degree

The number of geometric points in the kernel of a nonzero isogeny is its separable degree. So a separable isogeny has as many kernel points as its degree, and a purely inseparable one has trivial kernel.

Let $\alpha\colon E_1\to E_2$ be a nonzero [isogeny](isogeny-of-elliptic-curves.md) of elliptic curves over a field $k$, with [separable degree](frobenius-factorization-of-an-isogeny.md) $\deg_s\alpha$. Then

$$
\#\ker\alpha=\#\{P\in E_1(\bar k):\alpha(P)=O\}=\deg_s\alpha,
$$

and every fibre $\alpha^{-1}(Q)$, $Q\in E_2(\bar k)$, has exactly $\deg_s\alpha$ points. In particular, if $\alpha$ is separable then $\#\ker\alpha=\deg\alpha$, and if $\alpha$ is purely inseparable then $\ker\alpha=\{O\}$.

## Depends on

- [Isogeny of elliptic curves](isogeny-of-elliptic-curves.md)
- [In positive characteristic, every nonzero isogeny is a separable isogeny after a power of Frobenius](frobenius-factorization-of-an-isogeny.md)

## Proof depends on

None.

## Expansion

All fibres of a nonzero isogeny are cosets of its kernel, since it is a surjective group homomorphism, so they have the same size. The Frobenius $\pi^n$ is a bijection on $\bar k$-points, so one may assume $\alpha$ separable. In general a separable morphism of curves of degree $d$ has $d$ points in its generic fibre (Galbraith's proof of Lemma 9.6.4, through his Corollary 8.2.13), which with the coset remark gives $\#\ker\alpha=\deg\alpha$.

Sutherland gives an elementary proof for curves $y^2=f(x)$, in characteristic other than $2$ and $3$: write $\alpha=(u/v,\,(s/t)y)$ in standard form and pick a point $(a,b)$ in the image with $a,b\ne0$ and $a$ not the ratio of the leading coefficients of $u$ and $v$. Its preimages are determined by their $x$-coordinates, which are the roots of $g=u-av$, of degree $\deg\alpha$. Separability means $u'v-uv'\ne0$, so for all but finitely many choices of $(a,b)$ the roots of $g$ are simple and the fibre has $\deg\alpha$ points. A good expansion adds a page for the size of the generic fibre of a separable morphism of curves.

## Sources

- Andrew V. Sutherland, *18.783 Elliptic Curves*, MIT lecture notes, Spring 2021, [Lecture 5: Isogeny kernels and division polynomials](https://math.mit.edu/classes/18.783/2021/LectureNotes5.pdf), Theorem 5.8 and Corollary 5.9.
- Steven D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press (2012); extended and corrected version 2.0 of Chapter 9, [author's copy](https://www.math.auckland.ac.nz/~sgal018/crypto-book/ch9.pdf) (numbering of the extended version), Lemma 9.6.4 (separable case).
- Anamaria Costache, Brooke Feigon, Kristin Lauter, Maike Massierer, Anna Puskás, "Ramanujan graphs in cryptography", in *Research Directions in Number Theory (Women in Numbers IV)*, Association for Women in Mathematics Series 19, Springer (2019) 1–40, [doi:10.1007/978-3-030-19478-9_1](https://doi.org/10.1007/978-3-030-19478-9_1); numbers from arXiv:1806.05709v2, Lemma 2.3 (separable case).
- Luca De Feo, "Mathematics of Isogeny Based Cryptography", lecture notes, arXiv:1711.04062v1 (2017), Definition 24, item 3.

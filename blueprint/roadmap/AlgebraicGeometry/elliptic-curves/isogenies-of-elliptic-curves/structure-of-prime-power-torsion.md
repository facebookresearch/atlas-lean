# Structure of the prime-power torsion of an elliptic curve

Away from the characteristic, the $\ell^e$-torsion of an elliptic curve is a product of two cyclic groups of order $\ell^e$; at the characteristic $p$ it is cyclic of order $p^e$ or trivial.

Let $E$ be an elliptic curve over a field $k$ of characteristic $p\ge 0$, let $\ell$ be a prime and $e\ge 1$, and let $E[\ell^e]=\{P\in E(\bar k):\ell^eP=O\}$. Then

$$
E[\ell^e]\cong
\begin{cases}
\mathbb{Z}/\ell^e\mathbb{Z}\oplus\mathbb{Z}/\ell^e\mathbb{Z} & \text{if }\ell\ne p,\\
\mathbb{Z}/p^e\mathbb{Z}\ \text{or}\ \{0\} & \text{if }\ell=p .
\end{cases}
$$

Consequently, for every positive integer $n$ not divisible by $p$, $E[n]\cong\mathbb{Z}/n\mathbb{Z}\oplus\mathbb{Z}/n\mathbb{Z}$. When $k$ is an algebraic closure of the field with $p$ elements, $E[p^e]=\{O\}$ for every $e$ exactly when $E$ is [supersingular](../supersingular-elliptic-curves/is-supersingular.md).

## Depends on

- [Supersingular elliptic curves](../supersingular-elliptic-curves/is-supersingular.md)

## Proof depends on

- [In positive characteristic, every nonzero isogeny is a separable isogeny after a power of Frobenius](frobenius-factorization-of-an-isogeny.md)
- [The kernel of a nonzero isogeny has order its separable degree](kernel-order-equals-separable-degree.md)
- [Multiplication by m has degree m squared](degree-of-multiplication-by-m.md)
- [Supersingular curves have trivial prime-power torsion](../supersingular-elliptic-curves/pow-torsion.md)
- [Supersingularity from trivial prime-power torsion](../supersingular-elliptic-curves/of-pow-torsion.md)
- [Invariant factor decomposition of finite abelian groups](../../../GroupTheory/abelian-groups/structure-of-finitely-generated-abelian-groups/equiv-direct-sum-invariant-factors-of-fi.md)

## Expansion

For $\ell\ne p$, $[\ell^e]$ is separable of degree $\ell^{2e}$, so $\#E[\ell^e]=\ell^{2e}$. Every nonzero element of $E[\ell]$ has order $\ell$ and $\#E[\ell]=\ell^2$, so $E[\ell]$ has $\ell$-rank $2$; the $\ell$-rank of $E[\ell^e]$ equals that of $E[\ell]$, and a group of exponent dividing $\ell^e$, order $\ell^{2e}$ and rank $2$ is $(\mathbb{Z}/\ell^e)^2$. For $\ell=p$, $\deg_s[p]$ is $p$ or $1$, so $E[p]$ is $\mathbb{Z}/p$ or trivial; $E[p^e]$ has the same rank, at most $1$, and surjectivity of $[p]$ forces it to be all of $\mathbb{Z}/p^e$ when $E[p]\ne 0$. The coprime case follows from the Chinese remainder theorem over the prime powers dividing $n$. The last sentence combines the two supersingular pages listed above.

## Sources

- Andrew V. Sutherland, *18.783 Elliptic Curves*, MIT lecture notes, Spring 2021, [Lecture 6: Torsion subgroups and endomorphism rings](https://math.mit.edu/classes/18.783/2021/LectureNotes6.pdf), Theorem 6.1 and its proof.
- Luca De Feo, "Mathematics of Isogeny Based Cryptography", lecture notes, arXiv:1711.04062v1 (2017), Proposition 4.
- Denis X. Charles, Eyal Z. Goren, Kristin E. Lauter, "Cryptographic Hash Functions from Expander Graphs", *Journal of Cryptology* 22 (2009) 93–113, [doi:10.1007/s00145-007-9002-x](https://doi.org/10.1007/s00145-007-9002-x), Section 2.2.
- John Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer (2021), [doi:10.1007/978-3-030-56694-4](https://doi.org/10.1007/978-3-030-56694-4); numbers from the author's corrected edition v.1.0.7u, [author's copy](https://jvoight.github.io/quat-book.pdf), proof of Theorem 42.1.9.

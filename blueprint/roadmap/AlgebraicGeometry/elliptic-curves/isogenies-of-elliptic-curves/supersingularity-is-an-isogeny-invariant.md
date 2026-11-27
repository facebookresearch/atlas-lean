# Supersingularity is an isogeny invariant

If two elliptic curves over an algebraic closure of a prime field are related by a nonzero isogeny, both are supersingular or neither is.

Let $p$ be a prime, $\bar{\mathbb{F}}_p$ an algebraic closure of $\mathbb{F}_p$, and $\varphi\colon E_1\to E_2$ a nonzero [isogeny](isogeny-of-elliptic-curves.md) of elliptic curves over $\bar{\mathbb{F}}_p$. Then $E_1$ is [supersingular](../supersingular-elliptic-curves/is-supersingular.md) if and only if $E_2$ is.

## Depends on

- [Isogeny of elliptic curves](isogeny-of-elliptic-curves.md)
- [Supersingular elliptic curves](../supersingular-elliptic-curves/is-supersingular.md)

## Proof depends on

- [Every isogeny is a separable isogeny after a power of Frobenius](frobenius-factorization-of-an-isogeny.md)
- [The kernel of an isogeny has order its separable degree](kernel-order-equals-separable-degree.md)
- [Degrees of isogenies multiply under composition](degree-is-multiplicative.md)

## Expansion

Because $\varphi$ is a homomorphism, $[p]_{E_2}\circ\varphi=\varphi\circ[p]_{E_1}$. Taking separable degrees and using multiplicativity, $\deg_s[p]_{E_2}=\deg_s[p]_{E_1}$, so $\#E_1[p]=\#E_2[p]$ by the kernel count; supersingularity is the vanishing of $E[p]$. Sutherland proves the statement for curves over any field of characteristic $p$, with supersingular meaning $E[p]=0$ over the algebraic closure.

## Sources

- Andrew V. Sutherland, *18.783 Elliptic Curves*, MIT lecture notes, Spring 2019, [Lecture 14: Ordinary and supersingular elliptic curves](https://math.mit.edu/classes/18.783/2019/LectureNotes14.pdf), Theorem 14.2.
- Andrew V. Sutherland, *18.783 Elliptic Curves*, MIT lecture notes, Spring 2022, [Lecture 13: Ordinary and supersingular elliptic curves](https://math.mit.edu/classes/18.783/2022/LectureNotes13.pdf), Theorem 13.2.
- John Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer (2021), [doi:10.1007/978-3-030-56694-4](https://doi.org/10.1007/978-3-030-56694-4); numbers from the author's corrected edition v.1.0.7u, [author's copy](https://jvoight.github.io/quat-book.pdf), the paragraph before Lemma 42.1.11.

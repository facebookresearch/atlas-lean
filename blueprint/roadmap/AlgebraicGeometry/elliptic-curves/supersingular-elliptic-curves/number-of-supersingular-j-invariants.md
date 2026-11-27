# Number of supersingular j-invariants

In characteristic $2$ and $3$ there is one supersingular $j$-invariant. For a prime $p\ge5$ there are $\lfloor p/12\rfloor+\varepsilon_p$, where $\varepsilon_p$ is $0$, $1$, $1$, $2$ for $p\equiv1,5,7,11\pmod{12}$.

Let $p$ be a prime and $\bar{\mathbb{F}}_p$ an algebraic closure of $\mathbb{F}_p$. The number of isomorphism classes of [supersingular](is-supersingular.md) elliptic curves over $\bar{\mathbb{F}}_p$, equivalently of their $j$-invariants, is $1$ if $p=2$ or $p=3$, and for $p\ge 5$ it is

$$
\left\lfloor\frac{p}{12}\right\rfloor+\varepsilon_p,\qquad \varepsilon_p=\begin{cases}0&p\equiv1\pmod{12},\\1&p\equiv5,7\pmod{12},\\2&p\equiv11\pmod{12}.\end{cases}
$$

For example $p=5,7,11,13$ give $1,1,2,1$. In the notation of the supersingular $j$-invariant pages, this is the number of elements of the [set of supersingular $j$-invariants](../../../NumberTheory/not-yet-classified/supersingular-jset/ss-jset.md) $\operatorname{ssJSet}(p)$, and for every prime $p$ it equals the [supersingular count formula](../../../NumberTheory/not-yet-classified/supersingular-jset/ss-count-formula.md) at level $1$,

$$
\operatorname{ssCountFormula}(1,p)=\frac{p-1}{12}+\frac{2-\nu_2(p)}{4}+\frac{2-\nu_3(p)}{3},
$$

where $\nu_2(p)$ and $\nu_3(p)$ are the numbers of roots of $x^2+1$ and of $x^2+x+1$ in the field with $p$ elements.

## Depends on

- [Supersingular elliptic curves](is-supersingular.md)
- [Ss JSet](../../../NumberTheory/not-yet-classified/supersingular-jset/ss-jset.md)
- [Ss Count Formula](../../../NumberTheory/not-yet-classified/supersingular-jset/ss-count-formula.md)

## Proof depends on

- [The Eichler–Deuring mass formula for supersingular elliptic curves](eichler-deuring-mass-formula.md)
- [Automorphism groups of elliptic curves](../automorphism-group-of-an-elliptic-curve.md)
- [The Deuring correspondence between supersingular curves and maximal orders](../../../ComputerScience/cryptography/public-key/isogeny-and-lattice-foundations/supersingular-isogenies-and-quaternion-orders/deuring-correspondence.md)

## Expansion

One route is Deuring's: for $p$ odd the supersingular $\lambda$-values of the Legendre family are the roots of the Hasse invariant $H_p(\lambda)=\sum_{i=0}^{(p-1)/2}\binom{(p-1)/2}{i}^2\lambda^i$, which has distinct roots, and the map $\lambda\mapsto j$ is $6$-to-$1$ away from $j=0,1728$ (the route of Silverman, Theorem V.4.1, which Galbraith cites for the count). Another uses the mass formula: for $p\ge5$ let $a=1$ if $j=1728$ is supersingular and $b=1$ if $j=0$ is, else $0$; the curves with $j\ne0,1728$ have two automorphisms, so $(N-a-b)/2+a/4+b/6=(p-1)/24$ and $N=(p-1)/12+a/2+2b/3$. This is Voight's class number formula $(p-1)/12+\tfrac14\bigl(1-(\tfrac{-4}{p})\bigr)+\tfrac13\bigl(1-(\tfrac{-3}{p})\bigr)$, which agrees with $\operatorname{ssCountFormula}(1,p)$ for $p\ge5$ because $2-\nu_2(p)=1-(\tfrac{-4}{p})$ and $2-\nu_3(p)=1-(\tfrac{-3}{p})$ there; for $p=2$ and $p=3$ the whole formula $\operatorname{ssCountFormula}(1,p)$ evaluates to $1$, the count. Voight's formula is the case $D=p$, $M=1$ of his Eichler class number formula, Theorem 30.1.5. The mass-formula route gives the count once one knows that $j=1728$ is supersingular exactly when $p\equiv3\pmod4$ and $j=0$ exactly when $p\equiv2\pmod3$; that criterion needs a page of its own. The case analysis modulo $12$ then gives $\lfloor p/12\rfloor+\varepsilon_p$.

## Sources

- Steven D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press (2012); extended and corrected version 2.0 of Chapter 9, [author's copy](https://www.math.auckland.ac.nz/~sgal018/crypto-book/ch9.pdf) (numbering of the extended version), Theorem 9.11.12, item 1.
- Luca De Feo, "Mathematics of Isogeny Based Cryptography", lecture notes, arXiv:1711.04062v1 (2017), Theorem 47, item 2.
- John Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer (2021), [doi:10.1007/978-3-030-56694-4](https://doi.org/10.1007/978-3-030-56694-4); numbers from the author's corrected edition v.1.0.7u, [author's copy](https://jvoight.github.io/quat-book.pdf), Theorem 30.1.5 and paragraph 42.3.8.
- Denis X. Charles, Eyal Z. Goren, Kristin E. Lauter, "Cryptographic Hash Functions from Expander Graphs", *Journal of Cryptology* 22 (2009) 93–113, [doi:10.1007/s00145-007-9002-x](https://doi.org/10.1007/s00145-007-9002-x), Section 4.

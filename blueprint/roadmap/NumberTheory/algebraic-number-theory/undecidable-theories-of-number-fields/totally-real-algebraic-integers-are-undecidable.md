# The first-order theory of the ring of totally real algebraic integers is undecidable

Let $T$ be the field of all totally real algebraic numbers and $\mathcal{O}_T$ its ring of integers. The set of first-order sentences in the language of rings that are true in $\mathcal{O}_T$ is not computable, although the field $T$ itself has a decidable theory.

An algebraic number is *totally real* when every root of its minimal polynomial over $\mathbb{Q}$ is real. The totally real algebraic numbers form a field $T$, the maximal Galois extension of $\mathbb{Q}$ inside $\mathbb{R}$, equivalently the compositum of all number fields whose embeddings into $\mathbb{C}$ are all real; it is an infinite algebraic extension of $\mathbb{Q}$. Let $\mathcal{O}_T$ be the integral closure of $\mathbb{Z}$ in $T$, the ring of totally real algebraic integers. Work in the language of rings $\{+, \cdot, 0, 1\}$ with equality and without parameters.

**Theorem (J. Robinson).** The complete theory $\operatorname{Th}(\mathcal{O}_T)$ is undecidable.

The contrast with the field is part of the picture but not of the theorem: Fried, Haran and Völklein proved that the theory of the field $T$ is decidable, so $\mathcal{O}_T$ is not first-order definable in $T$.

## Depends on

- [Complete theory of a first-order structure](../../../Logic/first-order-logic/theory-of-structure.md)
- [Integral closure of ℤ in a field and the ring of integers of a number field](../number-fields-embeddings/ring-of-integers.md)

## Proof depends on

None.

## Expansion

Two ingredients. First, if an integral domain $R \supseteq \mathbb{N}$ has a uniformly parametrized family of subsets, given by one formula $\phi(x; \bar y)$, all of whose members are finite and which contains every initial segment $\{0, 1, \dots, n\}$ of $\mathbb{N}$, then $\mathbb{N}$ is definable in $R$: $n \in \mathbb{N}$ exactly when for some $\bar y$, $\phi(0; \bar y)$ holds and every $x$ with $\phi(x; \bar y)$ has $\phi(x + 1; \bar y)$ or $x = n$. Second, write $a \ll b$ when $b - a$ is totally positive, which in $T$ is expressible as $a \neq b \wedge \exists x\, (b = a + x^2)$. By Kronecker's theorem that an algebraic integer all of whose conjugates have absolute value at most $1$ is a root of unity, the totally real algebraic integers all of whose conjugates have absolute value at most $2$ are the numbers $\zeta + \zeta^{-1}$ with $\zeta$ a root of unity; hence the least real $M$ such that infinitely many $t \in \mathcal{O}_T$ satisfy $0 \ll t \ll M$ is $4$, attained by $2 + \zeta + \zeta^{-1}$ for roots of unity $\zeta$; for $M < 4$ the set $\{t : 0 \ll t \ll M\}$ is finite. The family of subsets of $\mathcal{O}_T$ defined by $0 \ll qx \ll p \wedge p \ll 4q$, with parameters $p, q$, therefore contains only finite sets, but arbitrarily large ones, and a variant of the first ingredient defines $\mathbb{N}$ from it. So $\mathbb{N}$, and with it $\mathbb{Z}$, is definable in $\mathcal{O}_T$, and the undecidability of the theory of $\mathbb{Z}$ transfers.

## Sources

- Julia Robinson, *On the decision problem for algebraic rings*, in: Studies in Mathematical Analysis and Related Topics (essays in honor of George Pólya, G. Szegő et al., eds.), Stanford University Press, Stanford, 1962, pp. 297–304; cited for attribution, with the statement and proof as read in Jochen Koenigsmann's survey below (Theorem 2.14 and Lemmas 2.15 and 2.16 of arXiv:1309.0441v1).
- Jochen Koenigsmann, *Undecidability in number theory*, in: Model Theory in Algebra, Analysis and Arithmetic, Lecture Notes in Mathematics 2111, Springer, 2014, pp. 159–195, https://doi.org/10.1007/978-3-642-54936-6_5; Theorem 2.14 of arXiv:1309.0441v1, with the two ingredients as Lemmas 2.15 and 2.16.
- Caleb Springer, *Definability and decidability for rings of integers in totally imaginary fields*, Bull. Lond. Math. Soc. 56 (2024), no. 1, 306–318, https://doi.org/10.1112/blms.12933, whose introduction (Section 1 of arXiv:2207.00140v3) recalls Robinson's theorem and the decidability of the field of totally real numbers due to Fried, Haran and Völklein.

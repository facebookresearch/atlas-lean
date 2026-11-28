# The first-order theories of a number field and of its ring of integers are undecidable

For every number field $K$, the ring of integers $\mathcal{O}_K$ is first-order definable in $K$ and $\mathbb{Z}$ is first-order definable in $\mathcal{O}_K$; consequently neither the set of sentences true in $\mathcal{O}_K$ nor the set true in $K$, in the language of rings, is computable.

Let $K$ be a number field, a field extension of $\mathbb{Q}$ of finite degree, and let $\mathcal{O}_K$ be its ring of integers. Work in the language of rings $\mathcal{L}_{\mathrm{ring}} = \{+, \cdot, 0, 1\}$ with equality, without parameters, and fix an effective Gödel numbering of its sentences.

**Theorem (J. Robinson).** For every number field $K$:

1. $\mathcal{O}_K$ is definable in the field $K$ by a first-order $\mathcal{L}_{\mathrm{ring}}$-formula, and $\mathbb{Z}$ is definable in the ring $\mathcal{O}_K$ by a first-order $\mathcal{L}_{\mathrm{ring}}$-formula;
2. the complete theories $\operatorname{Th}(\mathcal{O}_K)$ and $\operatorname{Th}(K)$ are undecidable.

The case $K = \mathbb{Q}$ includes the undecidability of the theory of $\mathbb{Q}$.

## Depends on

- [Complete theory of a first-order structure](../../../Logic/first-order-logic/theory-of-structure.md)
- [Integral closure of ℤ in a field and the ring of integers of a number field](../number-fields-embeddings/ring-of-integers.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The first-order theory of the ring of integers is undecidable](../../../Logic/proof-theory/g-del-s-incompleteness-theorems/first-order-theory-of-the-integers-is-undecidable.md)

## Expansion

The definition of $\mathcal{O}_K$ in $K$ follows Robinson's definition of $\mathbb{Z}$ in $\mathbb{Q}$, using quadratic forms and the Hasse–Minkowski local-global principle, which holds over every number field. To define $\mathbb{N}$ in $\mathcal{O}_K$, let $l = [K : \mathbb{Q}]$ and use that for every nonzero $f \in \mathcal{O}_K$ only finitely many $a \in \mathcal{O}_K$ satisfy $a + 1 \mid f, \dots, a + l \mid f$. With

$$
\rho(a, f, g, h) :\equiv f \neq 0 \wedge (a + 1 \mid f) \wedge \dots \wedge (a + l \mid f) \wedge (1 + ag \mid h),
$$

an element $n \in \mathcal{O}_K$ is a natural number exactly when there are $f, g, h$ with $\rho(0, f, g, h)$ such that every $a$ with $\rho(a, f, g, h)$ has $\rho(a + 1, f, g, h)$ or $a = n$. For $n \in \mathbb{N}$ one takes $f = (n + l)!$, a large natural number $g$ separating the finitely many candidates, and $h = (1 + g)(1 + 2g) \cdots (1 + ng)$. Since $\mathbb{Z} = \mathbb{N} \cup (-\mathbb{N})$ is then definable, sentences about $(\mathbb{Z}, +, \cdot, 0, 1)$ translate computably into sentences about $\mathcal{O}_K$, and by composing the definitions into sentences about $K$; the theory of $\mathbb{Z}$ is undecidable, so both theories are.

A good expansion adds and links pages for the Hasse–Minkowski principle for quadratic forms over number fields, for Robinson's first-order definition of $\mathcal{O}_K$ in $K$, and for the definition of $\mathbb{N}$ in $\mathcal{O}_K$ given above.

## Sources

- Julia Robinson, *The undecidability of algebraic rings and fields*, Proc. Amer. Math. Soc. 10 (1959), no. 6, 950–957, https://doi.org/10.1090/S0002-9939-1959-0112842-7; cited for attribution, with the statement and proof as read in Jochen Koenigsmann's survey below (Theorem 2.13 of arXiv:1309.0441v1).
- Jochen Koenigsmann, *Undecidability in number theory*, in: Model Theory in Algebra, Analysis and Arithmetic, Lecture Notes in Mathematics 2111, Springer, 2014, pp. 159–195, https://doi.org/10.1007/978-3-642-54936-6_5; Theorem 2.13 of arXiv:1309.0441v1, with the proof sketched above.

# The field of constructible numbers has undecidable first-order theory

The field of constructible numbers, the smallest subfield of the algebraic numbers closed under taking square roots of positive elements, has an undecidable first-order theory in the language of rings. This answers a question of Tarski from 1948.

Let $\mathbb{K}$ be the *field of constructible numbers*: the smallest subfield of the field of algebraic numbers that is closed under taking a square root of each of its positive elements. Its elements are real numbers, the lengths constructible with straightedge and compass from a unit length. Work in the language of rings $\{+, \cdot, 0, 1\}$ with equality.

**Theorem (Mazur–Rubin–Shlapentokh).** The first-order theory of the field $\mathbb{K}$ is undecidable.

The same argument gives undecidability of the first-order theory of each of the following fields: a non-big union of a tower of Galois extensions of a number field; a non-big Galois extension of a number field; a union of a tower of extensions of degree at most $d$, for a fixed $d \ge 2$; the compositum of all extensions of degree at most $d \ge 2$ of a number field; and the closure of a number field under taking $n$-th roots, or $2n$-th roots of positive elements. Here a field of algebraic numbers is big when it contains, for every $n$, a number field of degree divisible by $n$.

## Depends on

- [Complete theory of a first-order structure](../../../Logic/first-order-logic/theory-of-structure.md)
- [Field](../../../Algebra/rings-and-fields/field.md)
- [Subfield](../../../Algebra/rings-and-fields/subfield.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Rings of integers of non-big algebraic fields have undecidable first-order theory](integers-of-non-big-fields-are-undecidable.md)

## Expansion

$\mathbb{K}$ is the union of a tower of extensions of degree $2$ of $\mathbb{Q}$, so every number field inside it has degree a power of $2$; hence $\mathbb{K}$ is not big, and it is uniformly $p$-bounded for every odd prime $p$ in the sense of Shlapentokh's work on definability of rings of integers in infinite extensions. By that work the ring of integers $\mathcal{O}_{\mathbb{K}}$ is first-order definable in $\mathbb{K}$, and by the uniform definition of $\mathbb{Z}$ in rings of integers of non-big fields, $\mathbb{Z}$ is first-order definable in $\mathcal{O}_{\mathbb{K}}$. Composing the definitions defines $\mathbb{Z}$ in $\mathbb{K}$, and the undecidability of the theory of $\mathbb{Z}$ transfers. The other fields in the list are handled the same way, being non-big and uniformly $p$-bounded for a suitable prime $p$, for instance any $p > d$ for the compositum or a tower of extensions of degree at most $d$, and any $p > 2n$ for the closure under $n$-th or $2n$-th roots. A good expansion links pages for Shlapentokh's first-order definition of the ring of integers in a uniformly $p$-bounded field, and for the undecidability of the first-order theory of the ring $\mathbb{Z}$.

## Sources

- Barry Mazur, Karl Rubin and Alexandra Shlapentokh, *Defining $\mathbb{Z}$ using unit groups*, Acta Arith. 214 (2024), 235–255, https://doi.org/10.4064/aa230505-6-6; Corollary 1.11 (constructible numbers) and Corollary 1.10 (the further fields) with its proof, in Section 1.5 of arXiv:2303.02521v3.

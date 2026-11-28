# Rings of integers of non-big algebraic fields have undecidable first-order theory

Call a field of algebraic numbers big when, for every $n$, it contains a number field whose degree is divisible by $n$. One formula of the shape $\forall\forall\exists\cdots\exists$ defines $\mathbb{Z}$ in the ring of integers of every non-big field of algebraic numbers, so all these rings have undecidable first-order theory.

A *field of algebraic numbers* is a subfield $K$ of a fixed algebraic closure $\overline{\mathbb{Q}}$, possibly of infinite degree over $\mathbb{Q}$. It is *big* if

$$
[K : \mathbb{Q}] = \prod_{p \text{ prime}} p^{\infty},
$$

equivalently, if for every positive integer $n$ the field $K$ contains a number field $F$ with $n \mid [F : \mathbb{Q}]$. Let $\mathcal{O}_K$ be the integral closure of $\mathbb{Z}$ in $K$. Following the source, $\mathbb{Z}$ has a *uniform first-order definition* over the rings of integers of a class of fields when there are finitely many polynomials $P_1, \dots, P_\ell \in \mathbb{Z}[t, x_1, \dots, x_r]$ and quantifiers $E_1, \dots, E_r \in \{\forall, \exists\}$ such that, for every field $L$ of the class, an element $t \in \mathcal{O}_L$ satisfies $E_1 x_1 \cdots E_r x_r \bigwedge_{i=1}^{\ell} P_i(t, \bar x) = 0$ in $\mathcal{O}_L$ exactly when $t \in \mathbb{Z}$.

**Theorem (Mazur–Rubin–Shlapentokh).** Let $\mathcal{A}$ be the collection of all non-big fields of algebraic numbers. There is a uniform first-order definition of $\mathbb{Z}$, with quantifier prefix of the form $\forall \forall \exists \cdots \exists$, over the rings of integers $\mathcal{O}_K$ of all fields $K \in \mathcal{A}$. In particular, for every non-big field $K$ of algebraic numbers, the first-order theory of $\mathcal{O}_K$ is undecidable.

Conventions: every number field is non-big, so the theorem contains a uniform version of Julia Robinson's theorem for rings of integers of number fields.

## Depends on

- [Complete theory of a first-order structure](../../../Logic/first-order-logic/theory-of-structure.md)
- [Integral closure of ℤ in a field and the ring of integers of a number field](../number-fields-embeddings/ring-of-integers.md)
- [Field](../../../Algebra/rings-and-fields/field.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

One idea behind the proof is the identity $\frac{x^n - 1}{x - 1} \equiv n \pmod{x - 1}$ in $\mathbb{Z}[x]$: if $x$ is a unit of a ring of integers then so is $x^n$, and the residues $n$ modulo $x - 1$ recover rational integers from units, the same mechanism as in the Pell-equation methods of Julia Robinson, Davis, Denef and Lipshitz. The source first shows how to pass, by first-order formulas, from suitable definable submonoids of a ring of integers to definable subrings, and then computes the relevant objects for rings of integers of non-big fields, where for some prime the degrees of the number fields inside $K$ have bounded valuation. This yields one formula with prefix $\forall\forall\exists\cdots\exists$ that defines $\mathbb{Z}$ in all these rings. Since the theory of $\mathbb{Z}$ is undecidable, so is the theory of each $\mathcal{O}_K$. When $\mathcal{O}_K$ is also definable in $K$, the theory of $K$ is undecidable too; the source deduces in this way the undecidability of fields such as the field of constructible numbers. A good expansion links pages for the passage from definable submonoids of a ring of integers to definable subrings (Section 2 of the source), for the computation for non-big fields that proves Theorem 4.8 (Section 4), and for the undecidability of the first-order theory of the ring $\mathbb{Z}$.

## Sources

- Barry Mazur, Karl Rubin and Alexandra Shlapentokh, *Defining $\mathbb{Z}$ using unit groups*, Acta Arith. 214 (2024), 235–255, https://doi.org/10.4064/aa230505-6-6; Theorem 4.8, stated in Section 1.5 and proved in Section 4 of arXiv:2303.02521v3, with Definition 1.8 (big fields).

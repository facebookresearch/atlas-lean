# Separably closed fields are finitely undecidable

For every prime $p$ and every degree of imperfection $e$, finite or infinite, the complete theory of separably closed fields of characteristic $p$ and imperfection degree $e$ is finitely undecidable: although decidable, none of its finitely axiomatized subtheories is decidable.

**Setting.** For a prime $p$ and $e \in \mathbb{N}_{>0} \cup \{\infty\}$, $\mathsf{SCF}_{p,e}$ is the theory, in the language of rings, of separably closed fields of characteristic $p$ whose degree of imperfection $[K : K^p] = p^e$ (degree of imperfection $e$; for $e = \infty$, larger than every $n$). Each $\mathsf{SCF}_{p,e}$ is complete and decidable; the source states decidability in its Example 3.9 and, for both facts, refers to F. Delon, "Separably closed fields", in *Model Theory and Algebraic Geometry*, Lecture Notes in Mathematics 1696, Springer, 1999, pp. 143–177 (decidability at pp. 146–153).

**Theorem (Tyrrell).** Let $p$ be a prime. For every $e \in \mathbb{N}_{>0}$, $\mathsf{SCF}_{p,e}$ is [finitely undecidable](finitely-undecidable-theories.md) (Corollary 3.7), and $\mathsf{SCF}_{p,\infty}$ is finitely undecidable (Corollary 3.8).

The case $e = 0$, algebraically closed fields of characteristic $p$, is Ziegler's earlier result.

## Depends on

- [Finitely undecidable theories](finitely-undecidable-theories.md)
- [Complete theory of a first-order structure](../../../first-order-logic/theory-of-structure.md)
- [Field](../../../../Algebra/rings-and-fields/field.md)
- [Separable extension](../../../../FieldTheory/extensions-and-closure/separable-extension.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

Following Ziegler, for each prime $q \neq p$ one builds a field $K_q$ inside the separable closure of $\widetilde{\mathbb{F}_p(t)}(u_1, \dots, u_e)$ in which an undecidable structure is uniformly interpretable (Proposition 3.1); this construction does not depend on any theory. In the proof of Corollary 3.7, a nonprincipal ultraproduct $K$ of the $K_q$ is relatively separably closed in the corresponding ultrapower and has degree of imperfection exactly $e$ by Łoś's theorem, so $K$ satisfies $\mathsf{SCF}_{p,e}$ and hence any given finite subtheory $\Sigma$; as $\Sigma$ is finitely axiomatized, some $K_q$ satisfies $\Sigma$, and the hereditary undecidability of the theory of $K_q$ makes $\Sigma$ undecidable. For $e = \infty$, compactness reduces a finite subtheory to finitely many axioms on the imperfection degree, and the finite case applies.

## Sources

- B. Tyrrell, "Finite undecidability in NIP fields", *The Journal of Symbolic Logic* 90(2):509–532, 2025, doi:10.1017/jsl.2023.73; read as arXiv:2210.12729v4, <https://arxiv.org/abs/2210.12729v4>: Corollaries 3.7 and 3.8, Proposition 3.1 and Section 3 of arXiv:2210.12729v4.

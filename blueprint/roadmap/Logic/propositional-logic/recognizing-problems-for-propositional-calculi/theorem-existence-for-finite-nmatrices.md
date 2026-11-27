# Theorem existence for finite non-deterministic matrices is undecidable

No algorithm decides, given a finite non-deterministic logical matrix, whether the logic it defines has at least one theorem.

**Theorem (Caleiro, Filipe and Marcelino).** The problem [$\exists\mathsf{Thm}(\mathsf{NMatr})$](non-deterministic-logical-matrices.md), given a finite signature $\Sigma$ and a finite $\Sigma$-Nmatrix $\mathbb{M}$, to decide whether $\vdash_{\mathbb{M}}$ has a theorem, is undecidable (Theorem 13 of the source).

The source revisits this result from the authors' earlier work and uses it to prove that [equivalence of finite Nmatrices is undecidable](equivalence-of-finite-nmatrices-undecidable.md).

## Depends on

- [Non-deterministic logical matrices and their decision problems](non-deterministic-logical-matrices.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Halting is undecidable](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

From a counter machine $\mathcal{C}$ the proof builds a signature $\Sigma_{\mathcal{C}}$, with constants for zero and the empty configuration, a successor, and one connective per state, and a finite Nmatrix whose truth values are register values, configurations and two auxiliary values (Definition 8). Formulas describe computations, and $\mathcal{C}$ halts from all counters zero if and only if the Nmatrix has a theorem (Corollaries 11 and 12). The halting problem for counter machines (Minsky) is undecidable.

## Sources

- Carlos Caleiro, Pedro Filipe and Sérgio Marcelino, "Equivalence of finite non-deterministic logical matrices is undecidable", *Studia Logica*, 2025, doi:[10.1007/s11225-025-10212-x](https://doi.org/10.1007/s11225-025-10212-x). Numbering of the version read, arXiv:2412.14057v1: Theorem 13, Definition 8 and Corollaries 11 and 12, Section 3.

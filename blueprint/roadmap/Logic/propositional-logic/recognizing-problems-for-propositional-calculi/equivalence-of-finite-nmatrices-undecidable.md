# Equivalence of finite non-deterministic matrices is undecidable

No algorithm decides whether two finite non-deterministic logical matrices over the same finite signature define the same logic, although this is decidable for deterministic matrices.

**Theorem (Caleiro, Filipe and Marcelino).** The problem [$\mathsf{Eqv}(\mathsf{NMatr})$](non-deterministic-logical-matrices.md), given a finite signature $\Sigma$ and finite $\Sigma$-Nmatrices $\mathbb{M}_1$ and $\mathbb{M}_2$, to decide whether $\vdash_{\mathbb{M}_1} = \vdash_{\mathbb{M}_2}$, is undecidable (Theorem 20 of the source).

For finite deterministic matrices the equivalence problem is decidable, as the source recalls in Section 2.3.

## Depends on

- [Non-deterministic logical matrices and their decision problems](non-deterministic-logical-matrices.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Theorem existence for finite non-deterministic matrices is undecidable](theorem-existence-for-finite-nmatrices.md)

## Expansion

For a $\Sigma$-Nmatrix $\mathbb{M} = \langle V, D, \cdot\rangle$ the *tilded* Nmatrix $\widetilde{\mathbb{M}}$ adds a designated copy $\widetilde{x}$ of every undesignated value $x$ and lets each connective return all copies of the values it returned before (Definition 14). The logic of $\mathbb{M}$ has a theorem if and only if $\widetilde{\mathbb{M}}$ is not equivalent to the unconstrained two-valued Nmatrix $\mathbb{U}_\Sigma$, whose logic is $\Gamma \vdash A$ iff $A \in \Gamma$ (Corollaries 18 and 19). This computably reduces theorem existence to non-equivalence, so equivalence is undecidable.

## Sources

- Carlos Caleiro, Pedro Filipe and Sérgio Marcelino, "Equivalence of finite non-deterministic logical matrices is undecidable", *Studia Logica*, 2025, doi:[10.1007/s11225-025-10212-x](https://doi.org/10.1007/s11225-025-10212-x). Numbering of the version read, arXiv:2412.14057v1: Theorem 20, Definition 14, Example 2 and Corollaries 18 and 19, Section 4.

# Conservative extensions and uniform interpolants in Q¹S5 and Q¹K are undecidable

For the one-variable first-order modal logics $\mathsf{Q^1S5}$ and $\mathsf{Q^1K}$ with constant domains, deciding whether one formula is a (strong) conservative extension of another, and whether a formula has a uniform interpolant in a given signature, is undecidable, whereas the existence of ordinary interpolants is decidable.

**Theorem (Kurucz, Wolter and Zakharyaschev).** For the logics of the page on [one-variable first-order modal logics](one-variable-first-order-modal-logics-q1k-and.md):

1. the conservative extension problem and the strong conservative extension problem in $\mathsf{Q^1S5}$ are undecidable, and the uniform interpolant existence problem in $\mathsf{Q^1S5}$ is undecidable (Theorem 5.1);
2. the same three problems are undecidable in $\mathsf{Q^1K}$ (Theorem 7.5).

The inputs are the two formulas (for the (S)CEP) or a formula and a finite signature (for the UIEP). The conservative extension and uniform interpolant existence problems are also undecidable in the modal description logic $\mathsf{S5}_{\mathcal{ALC}^u}$ (Theorem 1.4 and Section 6). In contrast, interpolant and definition existence are decidable in coN2EXPTIME in $\mathsf{Q^1S5}$ (Theorem 1.2) and in non-elementary time in $\mathsf{Q^1K}$ (Theorem 1.5).

## Depends on

- [One-variable first-order modal logics Q¹K and Q¹S5](one-variable-first-order-modal-logics-q1k-and.md)

## Proof depends on

- [The tiling problem is undecidable](../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

The proof reduces an undecidable tiling problem, adapting an earlier undecidability proof for conservative extensions in two-variable first-order logic. For a tiling system one constructs in polynomial time formulas $\varphi$ and $\psi$ such that the system has a solution iff $\varphi \wedge \psi$ is not a (strong) conservative extension of $\varphi$; the new idea is to generate arbitrarily large binary trees inside $\mathsf{Q^1S5}$-models, which can be forced to be grids when the extension is not conservative. Combining the construction with an example in which a uniform interpolant fails to exist gives the UIEP; the same combination shows that uniform interpolant existence in two-variable first-order logic, with or without equality, is undecidable.

## Sources

- Agi Kurucz, Frank Wolter and Michael Zakharyaschev, "Deciding the existence of interpolants and definitions in first-order modal logic", *Logical Methods in Computer Science* 21(4):6, 2025, doi:10.46298/lmcs-21(4:6)2025; read as arXiv:2303.04598v4, <https://arxiv.org/abs/2303.04598v4>: Theorems 1.2, 1.4, 1.5, 5.1 and 7.5, and Sections 5, 6 and 7 of arXiv:2303.04598v4.

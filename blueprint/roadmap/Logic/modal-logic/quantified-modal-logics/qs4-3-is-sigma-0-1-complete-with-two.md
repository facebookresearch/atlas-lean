# QS4.3 and QK4.3.D.X are Σ⁰₁-complete with two variables and one monadic letter

The first-order modal logics of the rationals and the reals ordered by $\leq$ or $<$ are $\Sigma^0_1$-hard already for formulas with two individual variables, one monadic predicate letter and one proposition letter, and the finitely axiomatizable logics $\mathbf{QS4.3}$ and $\mathbf{QK4.3.D.X}$ are $\Sigma^0_1$-complete in that language.

**Theorem (Rybakov and Shkatov).** Consider [first-order modal logics of single frames](first-order-modal-logics-of-linear-frames.md) in the language with two individual variables, one monadic predicate letter and one proposition letter.

1. Let $\langle W, <\rangle$ be a strict linear order containing an infinite ascending chain of pairwise distinct elements, $\leq$ its reflexive closure, $R$ a relation between $<$ and $\leq$, and $L$ a logic with $\mathbf{L}(W, R) \subseteq L \subseteq \mathbf{L}_c(W, R)$. Then satisfiability for $L$ is $\Pi^0_1$-hard, so $L$ is $\Sigma^0_1$-hard (Theorem 5.2).
2. In particular $\mathbf{L}(\mathbb{Q}, \leq)$, $\mathbf{L}_c(\mathbb{Q}, \leq)$, $\mathbf{L}(\mathbb{Q}, <)$, $\mathbf{L}_c(\mathbb{Q}, <)$ and the corresponding four logics over $\mathbb{R}$ are $\Sigma^0_1$-hard (Corollary 5.3).
3. $\mathbf{QS4.3}$ and $\mathbf{QK4.3.D.X}$ are $\Sigma^0_1$-complete (Corollary 5.4), and so is $\mathbf{QK4.3}$ (Corollary 6.3).

## Depends on

- [First-order modal logics of single Kripke frames](first-order-modal-logics-of-linear-frames.md)
- [The arithmetical class $\Sigma_n$](../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)

## Proof depends on

- [The tiling problem is undecidable](../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

Hardness comes from a modification of the tiling construction used for $(\mathbb{N}, \leq)$: an infinite ascending chain suffices to represent the $\mathbb{N} \times \mathbb{N}$ grid, but without well-foundedness only the ordinary tiling problem can be encoded, giving $\Pi^0_1$-hardness of satisfiability. The source uses the $\Pi^0_1$-complete tiling problem for the quadrant $\mathbb{N} \times \mathbb{N}$ (Berger), which is equivalent by compactness to the tiling problem for the plane. Membership in $\Sigma^0_1$ holds because $\mathbf{QS4.3}$, $\mathbf{QK4.3.D.X}$ and $\mathbf{QK4.3}$ are finitely axiomatizable, and $\mathbf{QS4.3} = \mathbf{L}(\mathbb{Q}, \leq)$ and $\mathbf{QK4.3.D.X} = \mathbf{L}(\mathbb{Q}, <)$ by a result of Corsi, for which a good expansion would link a page; none exists yet.

## Sources

- M. Rybakov and D. Shkatov, "Algorithmic properties of first-order modal logics of linear Kripke frames in restricted languages", *Journal of Logic and Computation* 31(5):1266–1288, 2021, doi:10.1093/logcom/exab030; read as arXiv:2105.11811v1, <https://arxiv.org/abs/2105.11811v1>, whose numbering is used here: Theorem 5.2, Corollaries 5.3, 5.4 and 6.3, and Sections 5 and 6.

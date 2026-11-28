# Satisfiability of arbitrary public announcement logic with common knowledge is Σ¹₁-hard

Adding common knowledge to arbitrary, group or coalition announcement logic makes satisfiability Σ¹₁-hard, so neither the valid nor the satisfiable formulas of these logics are recursively enumerable and none of them has a finitary axiomatization.

**Theorem (Galimullin and Kuijer).** The satisfiability problems of the [logics APALC, GALC and CALC](quantified-announcement-logics-with-common.md), over models in which every agent's relation is an equivalence relation, are $\Sigma^1_1$-hard (Theorem 2 of the source). Consequently, the set of valid formulas of each of these logics is neither recursively enumerable nor co-recursively enumerable (Corollary 1), and none of the logics has a finitary axiomatization (Corollary 2).

Without common knowledge, satisfiability of APAL, GAL and CAL is undecidable, by reductions from a tiling problem ([satisfiability of quantified announcement logics is undecidable](../satisfiability-of-quantified-announcement-logics.md)). The source notes that its results do not generalize in any obvious way to arbitrary agent relations.

## Depends on

- [Quantified public announcement logics with common knowledge](quantified-announcement-logics-with-common.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Recognizability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)

## Proof depends on

None.

## Expansion

The proof reduces the recurring tiling problem, which is $\Sigma^1_1$-complete: given a finite set $T$ of tiles with a designated tile $\tau^*$, is there a tiling of $\mathbb N \times \mathbb N$ in which $\tau^*$ occurs infinitely often in the first column? A formula $\Psi_T$, using agents $h$, $v$ and $s$, is satisfiable iff $T$ tiles $\mathbb N \times \mathbb N$ (Lemmas 1 and 2); the quantifier $[!]$ forces the models of $\Psi_T$ to be grids. Then $\Psi_T \wedge \Box_{\{v, s\}}[\Box_{\{h, s\}}\neg p^*]\neg\Psi_T$ is satisfiable iff some tiling has $\tau^*$ infinitely often in the first column (Theorem 1): the formula $\Box_{\{h, s\}}\neg p^*$ holds exactly on the rows whose first-column tile is not $\tau^*$, so the announcement removes every row whose first-column tile is $\tau^*$; if $\tau^*$ occurs only finitely often, the rows above the last occurrence still form a tiled copy of $\mathbb N \times \mathbb N$, and if it occurs infinitely often in some tiling, no infinite grid survives in that model. Replacing $[!]$ by $[\{h, v, s\}]$ or $[\langle\{h, v, s\}\rangle]$ gives the results for GALC and CALC. Since $\Sigma^1_1$ strictly contains the co-recursively enumerable sets, the validities are not recursively enumerable. A good expansion links the $\Sigma^1_1$-completeness of the recurring tiling problem.

## Sources

- R. Galimullin and L. B. Kuijer, "Satisfiability of arbitrary public announcement logic with common knowledge is Σ¹₁-hard", in *Proceedings of the Conference on Theoretical Aspects of Rationality and Knowledge (TARK 2023)*, Electronic Proceedings in Theoretical Computer Science 379, 2023, pp. 260–271, <https://doi.org/10.4204/EPTCS.379.21>; read as arXiv:2307.05060v1, <https://arxiv.org/abs/2307.05060v1>: Section 1, Section 3 (Definition 3.2, Lemmas 1 and 2, Theorems 1 and 2, Corollaries 1 and 2).

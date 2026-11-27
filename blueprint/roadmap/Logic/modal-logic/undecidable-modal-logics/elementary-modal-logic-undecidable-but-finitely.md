# An elementary modal logic that is undecidable but finitely decidable

There is a universal first-order frame condition Γ₁ for which global satisfiability of modal formulas is undecidable, while global satisfiability in finite frames satisfying Γ₁ is decidable.

**Theorem (Michaliszyn, Otop and Witkowski).** There is a universal first-order sentence $\Gamma_1$ with equality, over one binary relation, such that the [global satisfiability problem](global-satisfiability-over-elementary-frames.md) $\mathcal K_{\Gamma_1}$-SAT for unimodal logic over the frames satisfying $\Gamma_1$ is undecidable, while the finite global satisfiability problem $\mathcal K_{\Gamma_1}$-FINSAT is decidable.

The source gives $\Gamma_1$ explicitly: $\Gamma^{\mathrm{two}}_1 \Rightarrow \Gamma^{\mathrm{irr}}_1 \wedge \Gamma^{\mathrm{trans}}_1 \wedge \Gamma^{\mathrm{grid}}_1$, where $\Gamma^{\mathrm{two}}_1$ says that there are two distinct worlds of out-degree at least $7$ (ramified worlds), $\Gamma^{\mathrm{irr}}_1$ is irreflexivity, $\Gamma^{\mathrm{trans}}_1$ makes $R$ transitive from ramified worlds, and $\Gamma^{\mathrm{grid}}_1$ is the grid condition of the universal frame condition with undecidable global satisfiability, weakened to the conclusion $yRz \vee xRz$. There are infinitely many pairwise non-equivalent universal sentences with this property, for instance $\Gamma_1$ conjoined with the absence of irreflexive $n$-cliques for any $n > 2$ (Proposition 12).

## Depends on

- [Global satisfiability over elementary frame classes](global-satisfiability-over-elementary-frames.md)

## Proof depends on

- [The tiling problem is undecidable](../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

*Undecidability of SAT.* Models of $\Gamma_1$ and a modal formula $\tau_1$ locally look like the infinite grid, as for the frame condition $\Gamma$, and the tiling of $\mathbb N \times \mathbb N$ reduces to $\mathcal K_{\Gamma_1}$-SAT (Lemma 8).

*Decidability of FINSAT.* In a finite model of $\Gamma_1$ with two or more ramified worlds, $R$ is transitive and acyclic on ramified worlds, so some ramified world $v$ has no ramified descendant, and the worlds reachable from $v$ form a model with a single ramified world. A structure with at most one ramified world satisfies $\Gamma_1$ trivially, so it remains to decide whether the modal formula has a finite model with at most one ramified world; this holds iff it has a tree model whose ramified worlds all have the same type, which an alternating polynomial-space algorithm decides (Lemma 7).

## Sources

- J. Michaliszyn, J. Otop and P. Witkowski, "Satisfiability vs. Finite Satisfiability in Elementary Modal Logics", in *Proceedings of the Third International Symposium on Games, Automata, Logics and Formal Verification (GandALF 2012)*, Electronic Proceedings in Theoretical Computer Science 96, 2012, pp. 141–154, <https://doi.org/10.4204/EPTCS.96.11>; numbers from arXiv:1210.2481v1, <https://arxiv.org/abs/1210.2481v1>: Theorem 1, Section 4 (definition of $\Gamma_1$, Lemmas 7 and 8) and Proposition 12.

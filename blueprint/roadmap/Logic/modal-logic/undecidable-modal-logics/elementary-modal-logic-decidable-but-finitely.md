# An elementary modal logic that is decidable but finitely undecidable

There is a universal first-order frame condition Γ₂ for which global satisfiability of modal formulas is decidable, while global satisfiability in finite frames satisfying Γ₂ is undecidable.

**Theorem (Michaliszyn, Otop and Witkowski).** There is a universal first-order sentence $\Gamma_2$ with equality, over one binary relation, such that the [global satisfiability problem](global-satisfiability-over-elementary-frames.md) $\mathcal K_{\Gamma_2}$-SAT for unimodal logic over the frames satisfying $\Gamma_2$ is decidable, while the finite global satisfiability problem $\mathcal K_{\Gamma_2}$-FINSAT is undecidable.

The source gives $\Gamma_2$ explicitly as $(\Gamma^{\mathrm{refram}}_2 \Rightarrow \Gamma^{\mathrm{grid}}_2) \wedge \Gamma^{\mathrm{trans}}_2$, where $\Gamma^{\mathrm{refram}}_2$ says that some world of out-degree at least $7$ is reflexive, and the transitivity and grid parts are those of $\Gamma_1$. There are infinitely many pairwise non-equivalent universal sentences with this property (Proposition 12). Equality is used in the proofs; whether it is necessary is left open.

## Depends on

- [Global satisfiability over elementary frame classes](global-satisfiability-over-elementary-frames.md)

## Proof depends on

None.

## Expansion

*Undecidability of FINSAT.* Finite models of $\Gamma_2$ and a suitable modal formula encode tilings of tori $\mathbb Z_m \times \mathbb Z_m$ (adjacency modulo $m$), which reduces the problem whether a domino system tiles some such torus, undecidable by Theorem 4 of the source, to $\mathcal K_{\Gamma_2}$-FINSAT (Corollary 10).

*Decidability of SAT.* Every formula satisfiable over $\mathcal K_{\Gamma_2}$ has a model based on a quasi-tree, a tree in which ramified worlds are also connected to all their descendants: unravel a model and add these edges. An alternating polynomial-space algorithm guesses such a model level by level (Lemma 11).

## Sources

- J. Michaliszyn, J. Otop and P. Witkowski, "Satisfiability vs. Finite Satisfiability in Elementary Modal Logics", in *Proceedings of the Third International Symposium on Games, Automata, Logics and Formal Verification (GandALF 2012)*, Electronic Proceedings in Theoretical Computer Science 96, 2012, pp. 141–154, <https://doi.org/10.4204/EPTCS.96.11>; numbers from arXiv:1210.2481v1, <https://arxiv.org/abs/1210.2481v1>: Theorem 2, Section 5 (definition of $\Gamma_2$, Corollary 10, Lemma 11), Theorem 4 and Proposition 12.

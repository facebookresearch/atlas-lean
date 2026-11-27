# Pushdown module checking with imperfect information against CTL is undecidable

Module checking open pushdown systems against CTL when the environment sees only part of the state is undecidable, even if the environment always sees the depth of the stack and the formula uses only EF, EX, AG and AX.

**Theorem (Bozzelli).** [Pushdown module checking](module-checking.md) with imperfect information against CTL is undecidable when restricted to open pushdown systems with visible stack content depth. That is, there is no algorithm that decides, given an OPD $\mathcal S$ with visible stack content depth and a CTL formula $\varphi$ in positive normal form, whether every strategy tree of the induced module $\mathcal M_{\mathcal S}$ (respecting the environment's imperfect information) satisfies $\varphi$. Undecidability holds even when $\varphi$ lies in the fragment $\mathrm{CTL}(\mathbf{EF}, \mathbf{EX}, \mathbf{AG}, \mathbf{AX})$ and $\mathcal S$ is *stable* and has only environment configurations.

Here stability is a uniformity condition: any two non-terminal pairs (control state, top stack symbol) with the same visible parts have matching internal, push and pop transitions whose targets, and pushed symbols, again have the same visible parts. The undecidability of pushdown module checking with imperfect information against CTL in general was known (Aminof, Murano and Vardi, CONCUR 2007); when the stack content itself is visible the problem is decidable and 2EXPTIME-complete. The result settles the intermediate case of visible stack depth.

## Depends on

- [Module checking](module-checking.md)
- [CTL formulas](../computation-tree-logic/formula.md)
- [Pushdown automaton](../../../TheoryOfComputation/context-free-languages/grammars-and-pushdown-automata/pushdown-automata/pda.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

For an instance $I = ((u^1_1, \ldots, u^1_n), (u^2_1, \ldots, u^2_n))$ of the Post correspondence problem one builds a stable OPD $\mathcal S$ with visible stack content depth and only environment configurations, and a formula $\varphi \in \mathrm{CTL}(\mathbf{EF}, \mathbf{EX}, \mathbf{AG}, \mathbf{AX})$, such that $I$ has no solution iff $\mathcal M_{\mathcal S} \models_r \varphi$ (Theorem 4). The proof first encodes the set of solutions of $I$ by suitable marked trees with witnesses, with some ideas taken from the undecidability of emptiness for alternating automata on nested trees (Alur, Chaudhuri and Madhusudan), and then builds $\mathcal S$ and a formula $\phi$ such that the strategy trees of $\mathcal S$ satisfying $\phi$ correspond to these marked trees (Lemma 4); since the environment cannot distinguish nodes with the same visible parts, its pruning is uniform across them, which is what the encoding exploits.

## Sources

- L. Bozzelli, "New results on pushdown module checking with imperfect information", in *Proceedings of the Second International Symposium on Games, Automata, Logics and Formal Verification (GandALF 2011)*, Electronic Proceedings in Theoretical Computer Science 54, 2011, pp. 162–177, <https://doi.org/10.4204/EPTCS.54.12>; numbers from arXiv:1106.1239v1, <https://arxiv.org/abs/1106.1239v1>: Section 4.1: Theorem 3, Theorem 4 and Lemma 4; Section 1 for the known cases.

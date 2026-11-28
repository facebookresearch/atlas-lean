# Satisfiability of strategy logic is highly undecidable

Satisfiability of strategy logic sentences over concurrent game structures is $\Sigma^1_1$-hard, hence not even arithmetical, and satisfiability on finite models is undecidable.

**Theorem (Mogavero, Murano, Perelli and Vardi).** For [strategy logic](strategy-logic.md):

1. the satisfiability problem, whether a given SL sentence holds at the initial state of some concurrent game structure (with countably many states and actions), is $\Sigma^1_1$-hard: every $\Sigma^1_1$ set many-one reduces to it, so it is undecidable and lies outside the arithmetical hierarchy;
2. the satisfiability problem on finite models, whether a given SL sentence holds in some concurrent game structure with finitely many states and actions, is undecidable.

The source states the same $\Sigma^1_1$-hardness for its boolean-goal fragment SL[BG]. By contrast, the one-goal fragment SL[1G] has a satisfiability problem decidable in 2EXPTIME, and SL does not have the bounded-tree model property: some satisfiable sentences have only models with infinitely many actions (Theorem 3.5); bounding the number of successors does not characterize bounded models, which the source defines by a finite set of actions (Section 3.1).

## Depends on

- [Strategy logic](strategy-logic.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

Clause 1 reduces from the recurrent domino problem: given finite tile types $D$ with horizontal and vertical matching relations and a distinguished type $t_0$, is there a tiling $\mathbb{N} \times \mathbb{N} \to D$ respecting the relations in which $t_0$ occurs infinitely often in the first row? Harel proved this problem $\Sigma^1_1$-complete. The source first gives a sentence $\varphi^{ord}$ whose models must contain an infinite strictly ordered structure (so SL lacks the bounded-tree model property), then builds sentences $\varphi^{grd}$, $\varphi^{til}$ and $\varphi^{rec}$ forcing a grid, a matching tiling, and recurrence of $t_0$; their conjunction is satisfiable iff the domino system has a recurrent solution. Clause 2 follows from Troquard and Walther's undecidability of finite satisfiability of ATL* with strategy contexts, which embeds into SL. A good expansion links pages for the analytical hierarchy, its level $\Sigma^1_1$ and the reductions that define hardness for it, which the statement uses.

## Sources

- F. Mogavero, A. Murano, G. Perelli and M. Y. Vardi, "Reasoning about strategies: on the satisfiability problem", *Logical Methods in Computer Science* 13(1), Paper 9, 2017, doi:10.23638/LMCS-13(1:9)2017; read as arXiv:1611.08541v3, <https://arxiv.org/abs/1611.08541v3>: Theorem 3.10 in Section 3.2 of arXiv:1611.08541v3 (clause 1), Theorem 4.3 in Section 4.1 (clause 2), Theorem 4.2 (SL[BG]), Theorem 3.5 (no bounded model property) and Theorem 5.13 (SL[1G] in 2EXPTIME).

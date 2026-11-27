# Iterated dominance frontiers are iterated joins

Let $G$ be a control-flow graph with an entry node that has no predecessors and from which every node is reachable, let $J^+$ be the [iterated join](converging-paths-and-join-sets.md) and $\mathrm{DF}^+$ the [iterated dominance frontier](dominance-frontiers.md). For every set $S$ of nodes that contains the entry node,

$$J^+(S) = \mathrm{DF}^+(S).$$

Consequently, treating the entry node as an assignment to every variable $V$, the set of nodes that need a $\varphi$-function for $V$ in [minimal SSA form](construction-of-minimal-ssa-form/translation-to-static-single-assignment-form.md), namely $J^+(S)$ for the set $S$ of nodes that assign to $V$, equals $\mathrm{DF}^+(S)$, and a worklist over $\mathrm{DF}$ places exactly the $\varphi$-functions of minimal SSA form.

**Proof.** $J(S) \subseteq \mathrm{DF}^+(S)$ for every $S$ by [the convergence lemma](converging-paths-meet-in-an-iterated-dominance.md), and induction on the iteration gives $J^+(S) \subseteq \mathrm{DF}^+(S)$, since $J(S \cup \mathrm{DF}^+(S)) \subseteq \mathrm{DF}^+(S \cup \mathrm{DF}^+(S)) = \mathrm{DF}^+(S)$. Conversely $\mathrm{DF}(S) \subseteq J(S)$ for sets containing the entry by [the entry lemma](dominance-frontiers-of-sets-containing-the-entr.md), and induction gives $\mathrm{DF}^+(S) \subseteq J^+(S)$.

## Depends on

- [Converging paths and join sets](converging-paths-and-join-sets.md)
- [Dominance frontiers](dominance-frontiers.md)
- [Translation to static single assignment form](construction-of-minimal-ssa-form/translation-to-static-single-assignment-form.md)

## Proof depends on

- [Converging paths meet in an iterated dominance frontier](converging-paths-meet-in-an-iterated-dominance.md)
- [Dominance frontiers of sets containing the entry are joins](dominance-frontiers-of-sets-containing-the-entr.md)

## Sources

- R. Cytron, J. Ferrante, B. K. Rosen, M. N. Wegman and F. K. Zadeck, "Efficiently computing static single assignment form and the control dependence graph", *ACM Transactions on Programming Languages and Systems* 13(4):451–490, 1991, Section 3 (the nodes that need $\varphi$-functions), Section 4.3 (Theorem 2 with its proof, equations (5) and (6)) and Section 5.1 (the worklist placement of $\varphi$-functions, Figure 11).

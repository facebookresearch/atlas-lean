# Module checking

Module checking asks whether an open system, whose states are split into system states and environment states, satisfies a branching-time specification against every environment, that is, in every computation tree obtained by pruning environment choices.

**Definition.** A *module* is $\mathcal M = \langle AP, S = S_{sy} \cup S_{en}, s_0, R, L\rangle$: a (possibly infinite) Kripke structure with states $S$ partitioned into *system states* $S_{sy}$ and *environment states* $S_{en}$, initial state $s_0$, transition relation $R$ and labelling $L : S \to 2^{AP}$. Let $T_{\mathcal M}$ be the computation tree obtained by unwinding $\mathcal M$ from $s_0$. A *strategy tree* (an environment's view of the execution) is a subtree $ST$ of $T_{\mathcal M}$ containing the root such that every node labelled by a system state keeps all its children, and every node labelled by an environment state that has children in $T_{\mathcal M}$ keeps at least one. $\mathcal M$ *reactively satisfies* a branching-time formula $\varphi$, written $\mathcal M \models_r \varphi$, if every strategy tree, labelled by $L$, satisfies $\varphi$. The *module checking problem* for a class of modules and a specification logic asks, given $\mathcal M$ and $\varphi$, whether $\mathcal M \models_r \varphi$.

*Imperfect information.* With a set of invisible variables, two nodes $x_1, x_2$ of $T_{\mathcal M}$ may be indistinguishable to the environment ($\mathrm{vis}(x_1) = \mathrm{vis}(x_2)$, comparing the visible parts of the states along the paths to them); strategy trees are then also required to keep $x_1$ iff they keep $x_2$.

*Pushdown modules.* An *open pushdown system* (OPD) $\mathcal S = \langle AP, Q, q_0, \Gamma, \flat, \Delta, \mu, \mathit{Env}\rangle$ has finitely many control states $Q$, a stack alphabet $\Gamma$ with bottom symbol $\flat$, internal, push and pop transitions $\Delta$, a labelling $\mu : Q \times (\Gamma \cup \{\flat\}) \to 2^{AP}$, and a set $\mathit{Env} \subseteq Q \times (\Gamma \cup \{\flat\})$ declaring which pairs (control state, top of stack) are environment configurations. It induces an infinite module $\mathcal M_{\mathcal S}$ on its configurations $(q, \alpha)$, $\alpha \in \Gamma^*\flat$, starting from $(q_0, \flat)$. Control states and stack symbols are sets of visible and invisible variables; the *stack content depth is visible* if no stack symbol consists entirely of invisible variables, so that the environment always sees how many symbols are on the stack.

Note that $\mathcal M \not\models_r \varphi$ is not the same as $\mathcal M \models_r \neg\varphi$: the former says only that some strategy tree violates $\varphi$.

## Depends on

- [Kripke model](../../modal-logic/kripke-semantics/kripke-model.md)
- [CTL formulas](../computation-tree-logic/formula.md)

## Proof depends on

None.

## Expansion

Module checking was introduced by Kupferman, Vardi and Wolper for finite-state modules: model checking verifies the full tree $T_{\mathcal M}$, the behavior against a maximal environment, while module checking also covers every environment that disables some of its choices. For CTL over finite-state modules it is EXPTIME-complete, and for pushdown modules with perfect information against CTL it is 2EXPTIME-complete.

## Sources

- L. Bozzelli, "New results on pushdown module checking with imperfect information", in *Proceedings of the Second International Symposium on Games, Automata, Logics and Formal Verification (GandALF 2011)*, Electronic Proceedings in Theoretical Computer Science 54, 2011, pp. 162–177, <https://doi.org/10.4204/EPTCS.54.12>; numbers from arXiv:1106.1239v1, <https://arxiv.org/abs/1106.1239v1>: Section 2 (modules, strategy trees with imperfect information, reactive satisfaction, open pushdown systems and visible stack content depth).
- A. Ferrante, A. Murano and M. Parente, "Enriched MU-Calculi Module Checking", *Logical Methods in Computer Science* 4(3), 2008, paper 1, <https://doi.org/10.2168/LMCS-4(3:1)2008>; numbers from arXiv:0805.3462v2, <https://arxiv.org/abs/0805.3462v2>: Section 2 and Section 7 (modules and the memoryless variant used there).

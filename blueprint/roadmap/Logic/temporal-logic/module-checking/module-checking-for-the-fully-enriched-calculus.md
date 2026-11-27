# Module checking for the fully enriched μ-calculus is undecidable

Checking a finite module against a formula of the μ-calculus with inverse programs, graded modalities and nominals, in the memoryless setting where the environment always makes the same choice at duplicate nodes, is undecidable.

**Theorem (Ferrante, Murano and Parente).** Formulas of the *fully enriched μ-calculus* are built, in positive normal form, from $\mathit{true}$, $\mathit{false}$, atomic propositions $p, \neg p$, nominals $o, \neg o$ and variables $y$ by $\vee$, $\wedge$, the graded modalities $\langle n, \alpha\rangle\varphi$ ("$\varphi$ holds in at least $n + 1$ $\alpha$-successors") and $[n, \alpha]\varphi$ ("$\varphi$ holds in all but at most $n$ $\alpha$-successors"), and the fixpoints $\mu y.\varphi$ and $\nu y.\varphi$, where $\alpha$ ranges over atomic programs $a$ and their inverses $a^-$ (with $R(a^-) = R(a)^{-1}$) and $n \ge 0$ is written in binary; nominals are interpreted as singleton sets of initial states. A *module* $\mathcal M = \langle W_s, W_e, W_0, R, L\rangle$ is a finite Kripke structure over the atomic programs with states split into system states $W_s$ and environment states $W_e$ (see [module checking](module-checking.md)). In the *memoryless* module checking problem, $\mathcal M \models_r \varphi$ holds iff $\varphi$ is satisfied by every Kripke structure obtained from the acyclic unwinding (computation graph) of $\mathcal M$ by disabling, at each environment node, some but not all of its outgoing transitions, the same choice being made at duplicate environment nodes. There is no algorithm that decides, given a finite module $\mathcal M$ and a fully enriched μ-calculus sentence $\varphi$, whether $\mathcal M \models_r \varphi$.

By contrast, module checking finite-state and pushdown systems against the hybrid graded μ-calculus, which has no inverse programs, is decidable: EXPTIME-complete for finite-state modules, and 2EXPTIME-complete in the formula and EXPTIME-complete in the system for pushdown modules (Theorems 2 and 3 of the source).

## Depends on

- [Module checking](module-checking.md)
- [Formulas of the modal μ-calculus](../../modal-logic/modal-calculus/mu-formula.md)

## Proof depends on

- [The tiling problem is undecidable](../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

The proof reduces the tiling problem for the quadrant. Bonatti and Peron gave, for a tile set $T = \{t_1, \ldots, t_m\}$ with horizontal and vertical constraints, a fully enriched μ-calculus formula $\varphi$ satisfiable only on grid models (with programs $l^-$ and $v$ for the horizontal and vertical successor) that encode a legal tiling; this showed satisfiability undecidable. Here one takes the module with only environment states $x_1, \ldots, x_m, y_1, \ldots, y_m$, initial states $x_1, \ldots, x_m$, $t_i$ true at $x_i$ and $y_i$, nominal $o_i$ at $x_i$, $v$-edges among the $x_j$ and among the $y_j$, and $l^-$-edges between the two groups. Every tiled grid arises as one of the pruned structures of this module, so $\mathcal M \models_r \neg\varphi$ iff no legal tiling exists.

## Sources

- A. Ferrante, A. Murano and M. Parente, "Enriched MU-Calculi Module Checking", *Logical Methods in Computer Science* 4(3), 2008, paper 1, <https://doi.org/10.2168/LMCS-4(3:1)2008>; numbers from arXiv:0805.3462v2, <https://arxiv.org/abs/0805.3462v2>: Section 2.2 (hybrid graded μ-calculus), Section 3 (modules), Section 7: Theorem 4 and its proof, Theorems 2 and 3.
- P. A. Bonatti and A. Peron, "On the undecidability of logics with converse, nominals, recursion and counting", *Artificial Intelligence* 158(1):75–96, 2004, <https://doi.org/10.1016/j.artint.2004.04.012>: the formula $\varphi$ and the undecidability of satisfiability of the fully enriched μ-calculus; not read directly here: this clause rests on its statement in the arXiv copy of the first source above (proof of Theorem 4).

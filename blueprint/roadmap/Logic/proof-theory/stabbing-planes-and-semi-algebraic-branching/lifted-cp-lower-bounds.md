# Cutting planes lower bounds for lifted formulas via real dag-like lifting

Let $m = n^{\Delta}$ for a large enough constant $\Delta$, and let $\mathrm{IND}_m : [m] \times \{0,1\}^m \to \{0,1\}$ be the index gadget: one party holds a pointer of $\log m = O(\log n)$ bits and the other $m = n^{\Delta}$ data bits, and the output is the addressed data bit. For every unsatisfiable CNF $F$ on $n$ variables, every triangle-DAG solving the falsified-clause search problem of the composed formula $F \circ \mathrm{IND}_m^{n}$ has size $n^{\Theta(w(F))}$, where $w(F)$ is the minimum width of a resolution refutation of $F$. Consequently, for every unsatisfiable $k$-CNF $F$ on $n$ variables there is an unsatisfiable $2k$-CNF $F'$ on $n^{O(1)}$ variables, an encoding of $F \circ \mathrm{IND}_m^{n}$, such that every cutting planes refutation of $F'$ has length at least $n^{\Omega(w(F))}$.

This is a size lower bound and does not control depth. The supercritical size-depth trade-offs for cutting planes need a newer width-depth lifting theorem for triangle-DAGs (de Rezende–Fleming–Janett–Nordström–Pang), which turns a small and shallow triangle-DAG into a narrow and shallow resolution refutation.

## Proof sketch

A cutting planes refutation of $F'$ of length $s$ yields, for the partition of the gadget variables between the two parties, a triangle-DAG of size $O(s)$ for the search problem, whose nodes are triangles: sets defined by comparing a linear form in the first party's variables with one in the second party's variables. The dag-like lifting argument for rectangle-DAGs extends to triangle-DAGs: each triangle is partitioned into structured rectangles, and pruning to blockwise dense parts turns a triangle-DAG of size $n^{d}$ into a resolution refutation of $F$ of width $O(d)$.

## Depends on

- [Resolution refutation](../../propositional-logic/resolution-size-and-width/is-resolution-refutation.md)
- [Composed functions, gadgets and lifting theorems](../../../TheoryOfComputation/communication-complexity/randomized-and-dag-like-lifting/composed-function-lifting.md)

## Proof depends on

- [Garg–Göös–Kamath–Sokolov: dag-like lifting from resolution width](../../../TheoryOfComputation/communication-complexity/randomized-and-dag-like-lifting/ggks-dag-lifting.md)

## Sources

- A. Garg, M. Göös, P. Kamath, D. Sokolov, "Monotone circuit lower bounds from resolution", STOC (2018); Theory of Computing 16 (2020) (Theorem 3.3, Corollary 3.4).
- S. F. de Rezende, N. Fleming, D. Janett, J. Nordström, S. Pang, "Truly supercritical trade-offs for resolution, cutting planes, monotone circuits, and Weisfeiler-Leman", STOC (2025), arXiv:2411.14267.

# Cutting planes lower bounds for lifted formulas via real dag-like lifting

For every unsatisfiable CNF $F$ on $n$ variables of resolution width $w(F)$, and a suitable gadget $g$ on $O(\log n)$ bits, every cutting planes refutation of the lifted formula $F \circ g^n$ has size $n^{\Omega(w(F))}$. Combined with formulas of polynomial-size resolution refutations but large width (after lifting), this yields exponential separations and the supercritical size-depth trade-offs for cutting planes.

## Proof sketch

A cutting planes refutation induces, for any partition of the variables, a rectangle-DAG-like structure whose nodes are triangles (sets defined by comparing a linear form in Alice's variables with one in Bob's variables). Dag-like lifting extends to such triangle-DAGs, converting a small refutation into a narrow resolution refutation of $F$.

## Depends on

- [Garg–Göös–Kamath–Sokolov: dag-like lifting from resolution width](../../../TheoryOfComputation/communication-complexity/randomized-and-dag-like-lifting/ggks-dag-lifting.md)
- [The stabbing planes proof system](stabbing-planes-system.md)

## Proof depends on

- [Garg–Göös–Kamath–Sokolov: dag-like lifting from resolution width](../../../TheoryOfComputation/communication-complexity/randomized-and-dag-like-lifting/ggks-dag-lifting.md)
- [The stabbing planes proof system](stabbing-planes-system.md)

## Sources

- A. Garg, M. Göös, P. Kamath, D. Sokolov, "Monotone circuit lower bounds from resolution", STOC (2018); Theory of Computing 16 (2020).
- S. F. de Rezende, N. Fleming, D. Janett, J. Nordström, S. Pang, "Truly supercritical trade-offs for resolution, cutting planes, monotone circuits, and Weisfeiler-Leman", STOC (2025), arXiv:2411.14267.

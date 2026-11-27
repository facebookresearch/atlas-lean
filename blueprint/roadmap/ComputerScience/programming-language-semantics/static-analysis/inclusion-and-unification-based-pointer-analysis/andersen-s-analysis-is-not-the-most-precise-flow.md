# Andersen's analysis is not the most precise flow-insensitive analysis

A flow-insensitive points-to analysis computes its result from the set of pointer operations of a program alone, so it must account for every program built from the same operations with any control flow between them. Executions start with undefined variables, never read a variable before it is assigned, and obtain pointer values only from the listed operations. Andersen's analysis is not the most precise such analysis. Consider the set of operations

$$a = \&c;\quad c = \&b;\quad b = \&a;\quad b = a;\quad {*}b = c;\quad d = {*}a.$$

1. The least solution of [Andersen's inclusion constraints](andersen-s-inclusion-constraints.md) for these operations has $c \in \mathrm{pt}(d)$.
2. In no execution of any program consisting of these operations, with any control flow between them, does $d$ point to $c$.

So the points-to fact $d \mapsto c$ in Andersen's result is spurious for every program with these operations. The reason is that $a$ may point to $b$ and $b$ may point to $c$, but not at the same time.

## Depends on

- [Andersen's inclusion constraints](andersen-s-inclusion-constraints.md)

## Sources

- A. Møller and M. I. Schwartzbach, *Static Program Analysis*, lecture notes, Aarhus University, version of October 15, 2026, <https://cs.au.dk/~amoeller/spa/>: Section 11.1 (variables are undefined initially, and the analyses assume that no variable is read before it is initialized), Section 11.2, the remark that Andersen's analysis is not the most precise possible flow-insensitive points-to analysis, and Exercise 11.5 (the example, due to Chakaravarthy, with parts (a) and (b) and the hint), together with Exercise 11.4 (imprecision caused by normalization, observed by Horwitz).

## Expansion

This page needs a source check before it is ready: part 2 is posed in the notes as an exercise with a hint, and has to be checked against Chakaravarthy's paper on the complexity of flow-insensitive points-to analysis, which also fixes the precise notion of the most precise flow-insensitive analysis.

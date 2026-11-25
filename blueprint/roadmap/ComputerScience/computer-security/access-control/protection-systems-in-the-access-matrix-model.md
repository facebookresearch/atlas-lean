# Protection systems in the access-matrix model

A *protection system* in the model of Harrison, Ruzzo and Ullman consists of a finite set of generic rights and a finite set of commands. A *configuration* is a triple $(S, O, P)$ of a finite set of subjects, a finite set of objects $O \supseteq S$ and an access matrix $P$ assigning to each pair $(s, o) \in S \times O$ a set of rights. Each command has formal parameters, a condition that is a conjunction of tests $r \in P[s, o]$, and a body that is a sequence of primitive operations: enter or delete a right in a cell, create or destroy a subject or an object. A configuration $Q$ *leaks* the right $r$ if some command applied to $Q$ enters $r$ into a cell that did not contain it, and $Q_0$ is *unsafe* for $r$ if some configuration reachable from $Q_0$ leaks $r$.

## Depends on

- [Reachability in a labelled transition system is transitive](../../process-calculi/labelled-transition-systems/trans.md)

## Sources

- M. A. Harrison, W. L. Ruzzo and J. D. Ullman, "Protection in operating systems", *Communications of the ACM* 19(8):461–471, 1976

# Safety is decidable for mono-operational protection systems

A protection system is *mono-operational* if the body of every command consists of a single primitive operation. For mono-operational protection systems the safety question (given a configuration and a generic right $r$, can some sequence of commands enter $r$ into a cell of the access matrix that did not contain it) is decidable, and deciding whether a leak is possible is in NP: if a leak exists, then a shortest leaking command sequence has length at most $|R|(|S_0| + 1)(|O_0| + 2) + 4 + |R|(2|S_0| + |O_0| + 2)$, where $R$ is the set of generic rights and $S_0$ and $O_0$ are the initial sets of subjects and objects. Such a sequence may contain one delete operation, removing the right from the cell it later leaks into, and one destroy and re-create of a subject or object, so delete and destroy operations cannot simply be dropped from it.

## Depends on

- [Protection systems in the access-matrix model](protection-systems-in-the-access-matrix-model.md)

## Sources

- M. A. Harrison, W. L. Ruzzo and J. D. Ullman, "Protection in operating systems", *Communications of the ACM* 19(8):461–471, 1976, Theorem 1
- M. V. Tripunitara and N. Li, "The foundational work of Harrison–Ruzzo–Ullman revisited", CERIAS Technical Report 2006-33, Purdue University, <https://ece.uwaterloo.ca/~tripunit/papers/hru-revisited-06.pdf>: Section 3, the counterexample to the monotonicity assumption and Theorem 1 with its corrected bound on the shortest leaky computation.

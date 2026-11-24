# Safety is decidable for mono-operational protection systems

A protection system is *mono-operational* if the body of every command consists of a single primitive operation. For mono-operational protection systems the safety question (given a configuration and a generic right $r$, can some sequence of commands enter $r$ into a cell of the access matrix that did not contain it) is decidable: if a leak exists, then one exists by a command sequence whose length is bounded by a computable function of the number of generic rights and of the initial numbers of subjects and objects, so a search over all sequences up to that length decides safety.

## Depends on

- [Protection systems in the access-matrix model](protection-systems-in-the-access-matrix-model.md)

## Sources

- M. A. Harrison, W. L. Ruzzo and J. D. Ullman, "Protection in operating systems", *Communications of the ACM* 19(8):461–471, 1976, Theorem 1

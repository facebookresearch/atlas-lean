# Supercritical trade-offs in proof complexity

A trade-off between two complexity measures $\mu_1, \mu_2$ of refutations (for example width and size, size and depth, or space and length) is **supercritical** if, for formulas $F$ on $n$ variables, minimizing $\mu_1$ forces $\mu_2$ beyond its worst-case upper bound over all refutations. For example, every unsatisfiable CNF on $n$ variables has a resolution refutation of depth at most $n$ and tree-like size less than $2^{n+1}$ (the decision-tree refutation, with at most $2^{n+1} - 1$ clauses); a size-depth trade-off is supercritical if refutations of size close to minimal must have depth $\omega(n)$, and **truly supercritical** if this holds with the threshold measured against the formula size rather than the number of variables.

## Depends on

- [Resolution refutation](../../propositional-logic/resolution-size-and-width/is-resolution-refutation.md)

## Sources

- A. A. Razborov, "A new kind of tradeoffs in propositional proof complexity", Journal of the ACM 63 (2016).
- S. F. de Rezende, N. Fleming, D. Janett, J. Nordström, S. Pang, "Truly supercritical trade-offs for resolution, cutting planes, monotone circuits, and Weisfeiler-Leman", STOC (2025), arXiv:2411.14267.

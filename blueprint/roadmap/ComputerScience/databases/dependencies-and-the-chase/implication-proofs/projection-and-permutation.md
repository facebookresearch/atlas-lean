# Projection and permutation of an inclusion dependency

Suppose an instance satisfies $R[A_1,\ldots,A_m]\subseteq S[B_1,\ldots,B_m]$. For every $k\geq 0$ and every injection $j:\{1,\ldots,k\}\to\{1,\ldots,m\}$, the same instance satisfies

$$
R[A_{j(1)},\ldots,A_{j(k)}]\subseteq S[B_{j(1)},\ldots,B_{j(k)}].
$$

The same indices are used on both sides, in the same order, with no repetition. They need not be increasing: the rule both drops and reorders columns. For each source row, keep its original target witness and read it at the selected positions. This works also for $k=0$; an inhabited source still needs a target row.

## Depends on

- [Syntax of an inclusion dependency](../ind.md)
- [Satisfaction of an inclusion dependency](../inclusion-dependencies-and-finite-implication.md)

## Proof depends on

- [A joint witness for a projected row](../holds-in-iff-exists-row.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, [*Foundations of Databases*](https://webdam.di.ens.fr/Alice/pdfs/all.pdf), Addison-Wesley, 1995, rule IND2 following Definition 9.1.1, p. 193.

# Conditional tables are a strong representation system for relational algebra

For every c-table $T$ over an attribute set $U$ and every relational algebra query $q$ over $U$, one can construct a
c-table $q(T)$ with $\mathrm{rep}(q(T)) = q(\mathrm{rep}(T))$, where $q(\mathrm{rep}(T)) = \{q(I) : I \in \mathrm{rep}(T)\}$.
Thus c-tables form a strong representation system for relational algebra. Codd tables do not: for the Codd table $T$
over $\{A\}$ with the single row $(x)$, the possible answers of $\sigma_{A=3}(T)$ are the empty relation and $\{(3)\}$,
and no Codd table represents exactly that set.

## Depends on

- [Conditional tables](conditional-tables.md)
- [Relational algebra queries](../relational-algebra/expr.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995; authors' web edition <http://webdam.inria.fr/Alice/pdfs/all.pdf>, the definition of strong representation systems and Example 19.1.1 (pp. 489–490), and Theorem 19.3.2 (p. 495).

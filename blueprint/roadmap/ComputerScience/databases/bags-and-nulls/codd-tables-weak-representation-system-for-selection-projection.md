# Codd tables are a weak representation system exactly up to selection and projection

For a set $\mathcal I$ of instances and a query language $\mathcal L$, write $\mathcal I \equiv_{\mathcal L} \mathcal J$
when $\bigcap\{q(I) : I \in \mathcal I\} = \bigcap\{q(I) : I \in \mathcal J\}$ for every query $q$ in $\mathcal L$. A
representation system is weak for $\mathcal L$ if for every representation $T$ and every $q \in \mathcal L$ some
representation $q(T)$ satisfies $\mathrm{rep}(q(T)) \equiv_{\mathcal L} q(\mathrm{rep}(T))$.

Codd tables form a weak representation system for the selection-projection fragment of relational algebra (selections
with equalities and inequalities, and projections). If union or join is added to that fragment, Codd tables no longer
form a weak representation system.

## Depends on

- [Conditional tables](conditional-tables.md)
- [Relational algebra queries](../relational-algebra/expr.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995; authors' web edition <http://webdam.inria.fr/Alice/pdfs/all.pdf>, the definitions of sure facts, $\mathcal L$-equivalence and weak representation systems (pp. 490–491), and Theorem 19.2.1 with its proof (pp. 491–492).

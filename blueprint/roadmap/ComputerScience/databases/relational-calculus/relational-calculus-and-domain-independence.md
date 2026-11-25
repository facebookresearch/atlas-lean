# Relational calculus and domain independence

A relational calculus query has the form $\{x_1, \dots, x_k \mid \varphi\}$ where $\varphi$ is a first-order
formula over the database schema with constants and equality. Under the natural semantics quantifiers range
over a fixed underlying domain; under the active-domain semantics they range over the active domain of the
instance together with the constants of $\varphi$. A formula is domain independent if its answer on an
instance is the same for every domain containing the active domain and the constants of $\varphi$.
Safe-range formulas form a decidable syntactic class, and every safe-range query is domain independent.

## Depends on

- [Tuple](../relational-algebra/tuple.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995 (authors' web edition), §5.3–5.4 and Theorem 5.4.6. <http://webdam.inria.fr/Alice/pdfs/all.pdf>

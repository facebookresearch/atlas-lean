# Project-join normal form

Let $U$ be a finite set of attributes and $\Sigma$ a set of functional, multivalued and join dependencies over $U$. The schema
$(U, \Sigma)$ is in *project-join normal form* (PJ/NF) when every join dependency implied by $\Sigma$ is implied by the key
dependencies $X \to U$ implied by $\Sigma$.

## Depends on

- [Join dependencies and multivalued dependencies](join-dependencies-and-multivalued-dependencies.md)
- [Functional dependency](../../functional-dependencies/fd.md)
- [A functional dependency holds in a relation](../../functional-dependencies/holds-in.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995; authors' web edition <http://webdam.inria.fr/Alice/pdfs/all.pdf>, Exercise 11.6 (p. 267), crediting the notion to Fagin (1979).

# Inclusion dependencies and finite implication

An inclusion dependency $R[A_1, \dots, A_k] \subseteq S[B_1, \dots, B_k]$ holds in an instance when the
projection of $R$ on $A_1, \dots, A_k$ is contained in the projection of $S$ on $B_1, \dots, B_k$.
A set $\Sigma$ of dependencies finitely implies $\sigma$ if every finite instance satisfying $\Sigma$
satisfies $\sigma$, and implies $\sigma$ (unrestricted implication) if every instance does.

Finite and unrestricted implication coincide for functional dependencies alone and for inclusion
dependencies alone, but differ for sets of functional and inclusion dependencies taken together; and the
implication problem for functional and inclusion dependencies together is undecidable.

## Depends on

- [Functional dependency](../functional-dependencies/fd.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995 (authors' web edition), Chapter 9, Theorems 9.2.3 and 9.2.4. <http://webdam.inria.fr/Alice/pdfs/all.pdf>

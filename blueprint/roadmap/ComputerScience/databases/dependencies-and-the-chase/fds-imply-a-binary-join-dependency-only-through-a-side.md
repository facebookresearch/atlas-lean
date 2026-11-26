# Functional dependencies imply a binary join dependency only through one of its sides

Let $U$ be a finite set of attributes, $\{X, Y, Z\}$ a partition of $U$, and $F$ a set of functional dependencies over
$U$. Then $F$ implies the join dependency $\bowtie[XY, XZ]$ (equivalently, the multivalued dependency
$X \twoheadrightarrow Y$) if and only if $F$ implies $X \to Y$ or $F$ implies $X \to Z$.

## Depends on

- [Join dependencies and multivalued dependencies](multivalued-and-join-dependencies/join-dependencies-and-multivalued-dependencies.md)
- [Entailment of functional dependencies](../functional-dependencies/entails.md)

## Proof depends on

- [Heath's theorem](../lossless-decomposition-and-normal-forms/join-project-eq-of-holds-in.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995; authors' web edition <http://webdam.inria.fr/Alice/pdfs/all.pdf>, Proposition 8.3.3 (p. 171).

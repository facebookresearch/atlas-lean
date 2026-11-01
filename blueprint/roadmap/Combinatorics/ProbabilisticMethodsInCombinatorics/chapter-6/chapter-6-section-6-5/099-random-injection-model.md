---
article_id: af_92f47c0a3387e1288b9c1d65
declaration: def
origin: cited
statement: formalized
lean: RandomInjection.CanonicalNegDepGraph
---

# Setup 6.5.4 (Random injection model)

Let $X$ and $Y$ be finite sets with $|X| \leq |Y|$. Let $f \colon X \to Y$ be an injection chosen uniformly at random. We can also represent $f$ by a complete matching $M$ from $X$ to $Y$ in $K_{X,Y}$. For a given matching $F$ (not necessarily complete) in $K_{X,Y}$, let $A_F$ denote the event that $F \subset M$. Let $F_1, \ldots, F_n$ be matchings in $K_{X,Y}$. The canonical negative dependency graph for the events $A_{F_1}, \ldots, A_{F_n}$ has one vertex for each event, and an edge between the events $A_{F_i}$ and $A_{F_j}$ ($i \neq j$) if $F_i$ and $F_j$ are not vertex disjoint.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.226 Probabilistic Methods in Combinatorics (Fall 2022), Chapter 6, Section 6.5](../../../../../sources/v1/ProbabilisticMethodsInCombinatorics.md)

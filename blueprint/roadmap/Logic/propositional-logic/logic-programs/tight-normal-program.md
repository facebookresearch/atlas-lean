# Tight normal program

A [finite ground normal logic program](normal-logic-program.md) $P$ over atoms $A$ is *tight* if there is a level mapping $\lambda : A \to \mathbb{N}$ such that, for every rule of $P$, the level of its head is larger than the level of every atom of its positive body. The negative bodies are unrestricted. Equivalently, the *positive dependency graph* of $P$, with an edge from the head of each rule to each atom of its positive body, has no cycle: a level mapping makes every edge decrease the level, and conversely the length of the longest path out of each atom of a finite acyclic graph is such a mapping.

A program whose rules all have empty positive bodies is tight; $p \leftarrow p$ is not.

## Depends on

- [Acyclic graph](../../../ComputerScience/graph-algorithms/traversal-and-connectivity/topological-sorting/is-acyclic.md)
- [Normal logic program](normal-logic-program.md)

## Sources

- V. Lifschitz, "Foundations of logic programming", in G. Brewka (ed.), *Principles of Knowledge Representation*, CSLI Publications, 1996, pp. 69–127, <https://www.cs.utexas.edu/~vl/papers/flp.ps>, Section 3.2, the definition before Proposition 3.5: tight programs by a level mapping, and the remark that programs without positive bodies are trivially tight.

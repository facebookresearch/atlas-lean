# Disjunctive inclusion dependencies

A disjunctive inclusion dependency is a first-order constraint whose body is a single atom and whose head is a disjunction of existentially quantified atoms, none of them repeating a variable; an inclusion dependency is the case of a single head atom.

**Definition.** Over a relational signature $\sigma$, a *disjunctive inclusion dependency* (DID) is a sentence

$$
\forall \vec{x}\, \Bigl( A(\vec{x}) \rightarrow \bigvee_{j=1}^{m} \exists \vec{y}_j\, B_j(\vec{x}_j, \vec{y}_j) \Bigr),
$$

where $m \ge 1$, $A$ and each $B_j$ are atoms over $\sigma$, no variable occurs twice in $A$ or in any $B_j$, and the variables $\vec{x}_j$ are among $\vec{x}$. A set of facts satisfies the DID if whenever $A(\vec{a})$ holds, some disjunct $B_j$ has a matching fact. A DID with $m=1$ is an [inclusion dependency](../dependencies-and-the-chase/ind.md), written as a tuple-generating dependency with a single body atom and a single head atom.

## Depends on

- [Syntax of an inclusion dependency](../dependencies-and-the-chase/ind.md)
- [Tuple- and equality-generating dependencies and the chase](../dependencies-and-the-chase/tuple-and-equality-generating-dependencies-and-the-chase.md)

## Proof depends on

None.

## Sources

- Antoine Amarilli, Michael Benedikt, Pierre Bourhis and Michael Vanden Boom, "Query answering with transitive and linear-ordered data", in *Proceedings of the 25th International Joint Conference on Artificial Intelligence (IJCAI 2016)*, pp. 893–898, 2016; extended journal version in *Journal of Artificial Intelligence Research* 63, pp. 191–264, 2018, doi:[10.1613/jair.1.11240](https://doi.org/10.1613/jair.1.11240); read in arXiv:1607.00813v1 ([arXiv](https://arxiv.org/abs/1607.00813v1)), the conference article with its appendix: the definitions of inclusion dependencies and disjunctive inclusion dependencies in Section 2 of that version.

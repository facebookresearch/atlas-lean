# Labelled sample compression scheme

Let $C$ be a class of functions $X \to \beta$ and $k \in \mathbb{N}$. A sample compression scheme of size $k$ for $C$ consists of a compression map, sending every finite labelled sample $S = ((x_1,y_1), \dots, (x_m,y_m))$ to a list $I$ of indices in $\{1, \dots, m\}$ (repetitions allowed, order significant), and a reconstruction map, sending every finite list of labelled examples to a hypothesis $X \to \beta$, such that for every sample $S$ realizable by $C$ the list $I$ has length at most $k$ and the hypothesis reconstructed from $(S_i)_{i \in I}$ labels every example of $S$ correctly. The reconstructed hypothesis need not belong to $C$. A general (agnostic) scheme of size $k$ only requires that every compressed list have length at most $k$.

## Depends on

- [The realizable distribution family](../occam-bound-for-consistent-learners/realizable-family.md)

## Sources

- N. Littlestone and M. K. Warmuth, "Relating Data Compression and Learnability", unpublished manuscript, 1986.
- S. Floyd and M. K. Warmuth, "Sample Compression, Learnability, and the Vapnik-Chervonenkis Dimension", Machine Learning, 1995.

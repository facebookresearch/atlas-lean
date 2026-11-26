# Distributional search problem with hidden state

A *distributional search problem* consists of a discrete distribution $D$ on a set of states, an observation map $\mathrm{obs}$ from states to inputs, and an acceptance relation $\mathrm{acc}$ between states and outputs. For a randomized solver $A$ from inputs to outputs, the success experiment draws a state $z \sim D$, runs $A$ on $\mathrm{obs}(z)$ and accepts iff $\mathrm{acc}(z, A(\mathrm{obs}(z)))$; the solver sees only the observation, while the success test may use the hidden state (as in recovering a planted object). Ordinary distributional relation search is the case $\mathrm{obs} = \mathrm{id}$ with $\mathrm{acc}$ a relation on inputs and outputs. For a family of problems indexed by $n$, a class of admitted programs and an evaluator, the family *has a solver with error* $\varepsilon(n)$ if a single admitted program fails with probability at most $\varepsilon(n)$ at every $n$; this is monotone in the error bound and in the admitted class, and transfers along compilers that preserve admissibility and output laws.

## Depends on

- [Search problems: FNP, FP and TFNP](../../../TheoryOfComputation/complexity-classes/total-search-problems/search-problems-fnp-fp-and-tfnp.md)

## Sources

- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.

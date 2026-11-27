# Supported models

Let $P$ be a [finite ground normal logic program](normal-logic-program.md). An interpretation $I$ is *supported* by $P$ if every atom $a \in I$ is the head of some rule of $P$ whose body is [true in $I$](models-of-a-normal-logic-program.md). A *supported model* of $P$ is a model of $P$ that is supported by $P$.

Supported models need not be minimal: the program $p \leftarrow p$ has the supported models $\emptyset$ and $\{p\}$.

## Depends on

- [Normal logic program](normal-logic-program.md)
- [Models of a normal logic program](models-of-a-normal-logic-program.md)

## Sources

- P. Hitzler, *Operator-based semantics for logic programs*, lecture notes, TU Dresden, winter semester 2004/05, <https://people.cs.ksu.edu/~hitzler/topics/teaching/ws04/plecture.pdf>, Definition 2.17 (after Apt, Blair and Walker) and Program 2.20.
- V. Lifschitz, "Foundations of logic programming", in G. Brewka (ed.), *Principles of Knowledge Representation*, CSLI Publications, 1996, pp. 69–127, <https://www.cs.utexas.edu/~vl/papers/flp.ps>, Section 3.1 (sets of literals supported by a program, defined just before Proposition 3.3).

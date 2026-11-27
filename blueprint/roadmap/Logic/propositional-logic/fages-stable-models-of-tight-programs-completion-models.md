# Fages: stable models of tight programs = completion models

Let $P$ be a finite ground normal logic program. If $P$ is tight, that is, its positive dependency graph
(an edge from the head of each rule to every atom of its positive body) has no cycle, then the stable
models of $P$ are exactly the models of its Clark completion. Tightness cannot be dropped in general:
the program $p \leftarrow p$ has the completion $p \leftrightarrow p$, with models $\emptyset$ and $\{p\}$,
but its only stable model is $\emptyset$. This example shows that the conclusion can fail for non-tight
programs, not that every non-tight program is a counterexample.

## Depends on

- [Stable models of a normal logic program](../../TheoryOfComputation/np-completeness/satisfiability/stable-model-existence/is-stable-model.md)
- [Clark completion of a normal program](logic-programs/clark-completion-of-a-normal-program.md)
- [Tight normal program](logic-programs/tight-normal-program.md)

## Proof depends on

- [Stable models of tight programs are the supported models](logic-programs/stable-models-of-tight-programs-are-the-supported-models.md)
- [Models of the completion are the supported models](logic-programs/models-of-the-completion-are-the-supported-models.md)

## Sources

- V. Lifschitz, *Twelve definitions of a stable model*, ICLP 2008, LNCS 5366, 37–51, Section 8: for tight programs, stable models coincide with the Herbrand models of the completion, attributed there to F. Fages, *Consistency of Clark's completion and existence of stable models*, Methods of Logic in Computer Science 1 (1994) 51–60. <https://www.cs.utexas.edu/~vl/papers/12defs.pdf>

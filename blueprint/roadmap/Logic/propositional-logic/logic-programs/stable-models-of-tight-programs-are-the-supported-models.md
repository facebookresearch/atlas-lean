# Stable models of tight programs are the supported models

Let $P$ be a [tight](tight-normal-program.md) finite ground normal logic program. An interpretation is a [stable model](../../../TheoryOfComputation/np-completeness/satisfiability/stable-model-existence/is-stable-model.md) of $P$ if and only if it is a [supported model](supported-models.md) of $P$. Tightness cannot be dropped: the supported model $\{p\}$ of $p \leftarrow p$ is not stable.

**Proof sketch.** [Stable models are supported models](stable-models-are-supported-models.md). Conversely, let $M$ be a supported model and $\lambda$ a level mapping witnessing tightness. By induction on $\lambda(a)$, every $a \in M$ lies in the least model of the [reduct](../../../TheoryOfComputation/np-completeness/satisfiability/stable-model-existence/reduct.md) $P^M$: a supporting rule of $a$ has a positive body in $M$ of smaller levels and a negative body disjoint from $M$, so it survives in $P^M$. Hence $M$ is contained in the least model of $P^M$; and since $M$ is a model of $P$, it is a model of $P^M$, so equality holds.

## Depends on

- [Tight normal program](tight-normal-program.md)
- [Stable models of a normal logic program](../../../TheoryOfComputation/np-completeness/satisfiability/stable-model-existence/is-stable-model.md)
- [Supported models](supported-models.md)

## Proof depends on

- [Stable models are supported models](stable-models-are-supported-models.md)
- [Gelfond–Lifschitz reduct](../../../TheoryOfComputation/np-completeness/satisfiability/stable-model-existence/reduct.md)

## Sources

- V. Lifschitz, "Foundations of logic programming", in G. Brewka (ed.), *Principles of Knowledge Representation*, CSLI Publications, 1996, pp. 69–127, <https://www.cs.utexas.edu/~vl/papers/flp.ps>, Proposition 3.5 (for tight programs, answer sets are the consistent sets that are closed under the program and supported by it) and Problem 3.5.

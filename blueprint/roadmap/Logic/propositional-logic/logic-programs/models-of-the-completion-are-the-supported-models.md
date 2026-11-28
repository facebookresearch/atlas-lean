# Models of the completion are the supported models

Let $P$ be a [finite ground normal logic program](normal-logic-program.md). An interpretation is a model of the [Clark completion](clark-completion-of-a-normal-program.md) of $P$ if and only if it is a [supported model](supported-models.md) of $P$.

**Proof.** The implications from right to left in the completion say that the interpretation is a [model](models-of-a-normal-logic-program.md) of $P$, and the implications from left to right say that each true atom has a rule whose body is true.

## Depends on

- [Normal logic program](normal-logic-program.md)
- [Clark completion of a normal program](clark-completion-of-a-normal-program.md)
- [Supported models](supported-models.md)

## Proof depends on

- [Models of a normal logic program](models-of-a-normal-logic-program.md)

## Sources

- V. Lifschitz, "Foundations of logic programming", in G. Brewka (ed.), *Principles of Knowledge Representation*, CSLI Publications, 1996, pp. 69–127, <https://www.cs.utexas.edu/~vl/papers/flp.ps>, Proposition 3.19 (a model of the completion is an interpretation that is closed under the program and supported by it).

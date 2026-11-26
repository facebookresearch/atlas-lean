# Completeness of refinement mappings

Let $S_1$ and $S_2$ be specifications in the sense of Abadi and Lamport, with $S_1$ [machine closed](machine-closure-and-internal-continuity.md) and $S_2$ internally continuous and finitely invisibly nondeterministic. If $S_1$ implements $S_2$, then there are a specification $S_1^h$ obtained from $S_1$ by [adding a history variable](adding-a-history-variable.md), a specification $S_1^{hp}$ obtained from $S_1^h$ by [adding a prophecy variable](adding-a-prophecy-variable.md), and a [refinement mapping](../../refinement/refinement-mappings-prove-implementation.md) from $S_1^{hp}$ to $S_2$. Each hypothesis is needed: the source gives specifications violating one of them for which no such auxiliary variables and refinement mapping exist.

## Depends on

- [Machine closure, finite invisible nondeterminism and internal continuity](machine-closure-and-internal-continuity.md)
- [Adding a history variable](adding-a-history-variable.md)
- [Adding a prophecy variable](adding-a-prophecy-variable.md)

## Proof depends on

- [History variables preserve the externally visible property](history-variables-preserve-the-externally-visible-property.md)
- [Prophecy variables preserve the externally visible property](prophecy-variables-preserve-the-externally-visible-property.md)

## Sources

- M. Abadi and L. Lamport, *The Existence of Refinement Mappings*, SRC Research Report 29, Digital Equipment Corporation, 1988, <https://lamport.azurewebsites.net/pubs/abadi-existence.pdf>; journal version in *Theoretical Computer Science* 82(2):253–284, 1991, Section 7, Theorem 2, and the counterexamples in Sections 5 and 6.

# Completeness of refinement mappings

Let $S_1$ and $S_2$ be specifications in the sense of Abadi and Lamport, with $S_1$ [machine closed](machine-closure-and-internal-continuity.md) and $S_2$ internally continuous and finitely invisibly nondeterministic. If $S_1$ implements $S_2$, then there are a specification $S_1^h$ obtained from $S_1$ by [adding a history variable](adding-a-history-variable.md), a specification $S_1^{hp}$ obtained from $S_1^h$ by [adding a prophecy variable](adding-a-prophecy-variable.md), and a [refinement mapping](../../refinement/refinement-mappings-prove-implementation.md) from $S_1^{hp}$ to $S_2$. Each hypothesis is needed for these definitions, in which a prophecy variable must satisfy the finiteness condition P6: the source gives specifications violating one of them for which no such auxiliary variables and refinement mapping exist.

## Depends on

- [Machine closure, finite invisible nondeterminism and internal continuity](machine-closure-and-internal-continuity.md)
- [Adding a history variable](adding-a-history-variable.md)
- [Adding a prophecy variable](adding-a-prophecy-variable.md)
- [Refinement mappings prove implementation](../../refinement/refinement-mappings-prove-implementation.md)

## Proof depends on

- [History variables preserve the externally visible property](history-variables-preserve-the-externally-visible-property.md)
- [Prophecy variables preserve the externally visible property](prophecy-variables-preserve-the-externally-visible-property.md)

## Sources

- M. Abadi and L. Lamport, "The existence of refinement mappings", *Theoretical Computer Science* 82(2):253–284, 1991, <https://doi.org/10.1016/0304-3975(91)90224-P>; the numbered locators refer to the research report version, SRC Research Report 29, Digital Equipment Corporation, 1988, <https://lamport.azurewebsites.net/pubs/abadi-existence.pdf>, Section 7, Theorem 2; the counterexamples are in Section 2.3 (machine closure), Section 5.2 (finite invisible nondeterminism, with the remark that weakening P6 would avoid that example only by assuming the implementation to be proved) and Section 6 (internal continuity).

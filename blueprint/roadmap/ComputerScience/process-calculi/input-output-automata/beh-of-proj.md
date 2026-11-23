# Pasting behaviours of the components of a composition

Let $A_1$ and $A_2$ be [input/output automata](ioautomaton.md) with [strongly compatible](strongly-compatible.md) signatures and $A_1 \| A_2$ their [composition](compose-automata.md). A finite sequence $\beta$ of external actions of $A_1 \| A_2$ whose projections $\beta|\mathrm{sig}(A_1)$ and $\beta|\mathrm{sig}(A_2)$ are finite [behaviours](beh.md) of $A_1$ and $A_2$ is a finite behaviour of $A_1 \| A_2$ (Lynch and Tuttle, 1989, Proposition 3, which they state for schedules and then "when acts() and scheds() are replaced by ext() and behs()"; here for two automata and finite behaviours). With [the projection of behaviours](beh-proj-left.md), the finite behaviours of a composition are exactly the sequences of its external actions whose projections are behaviours of the components: trace semantics is compositional.

**Proof.** Take executions of the components with the two behaviours and interleave them: a leading internal action of either component is taken alone, which is possible because internal actions of one component are not actions of the other (strong compatibility); otherwise the next action of $\beta$ is taken by every component that has it. The induction is on the total length of $\beta$ and the two executions.

## Informally uses

- [External actions of a composition in its first component](mem-ext-compose-and-acts-left.md) and [External actions of a composition in its second component](mem-ext-compose-and-acts-right.md): an external action of the composition that belongs to a component is external there.
- [Internal actions are not external](not-mem-ext-of-mem-int.md): internal actions taken alone do not appear in the behaviour.

## Background

- [Strongly compatible signatures](strongly-compatible.md): internal actions are private.

## Sources

- N. A. Lynch, M. R. Tuttle, *An introduction to input/output automata*, CWI Quarterly 2(3), 1989, 219–246: Proposition 3.

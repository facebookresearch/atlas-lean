# Input/output automata

The input/output automaton model of Lynch and Tuttle: a labelled transition system whose actions are split into inputs, outputs and internal actions, and which accepts every input in every state. Automata compose by synchronizing on shared actions, each output being controlled by one component only. The finite schedules (respectively behaviours, or traces) of a composition are exactly the sequences of its actions (respectively external actions) whose projections are schedules (respectively behaviours) of the components, which makes trace semantics compositional. Below, automata are composed two at a time and executions, schedules and behaviours are finite; the source also composes countable families and treats fairness (through a partition of the locally controlled actions) and infinite executions.

- [Action signature](action-sig.md)
- [Actions of a signature](acts.md)
- [External actions of a signature](ext.md)
- [Non-internal actions are external](mem-ext-of-mem-acts.md)
- [Internal actions are not external](not-mem-ext-of-mem-int.md)
- [Strongly compatible signatures](strongly-compatible.md)
- [Composition of action signatures](compose-signatures.md)
- [Actions of a composed signature](acts-compose.md)
- [External actions of a composition](mem-acts-of-mem-ext-compose.md)
- [External actions of a composition in its first component](mem-ext-compose-and-acts-left.md)
- [External actions of a composition in its second component](mem-ext-compose-and-acts-right.md)
- [Projection onto a signature](proj.md)
- [External projection](ext-proj.md)
- [Projection onto the first component and external projection commute](proj-ext-proj-compose-left.md)
- [Projection onto the second component and external projection commute](proj-ext-proj-compose-right.md)
- [Input/output automaton](ioautomaton.md)
- [Finite schedule of an I/O automaton](sched.md)
- [Finite behaviour of an I/O automaton](beh.md)
- [Component move in a composition](move-or-stay.md)
- [Composition of I/O automata](compose-automata.md)
- [Projection of an execution of a composition onto its first component](m-tr-proj-left.md)
- [Projection of an execution of a composition onto its second component](m-tr-proj-right.md)
- [Pasting executions of the components of a composition](m-tr-of-proj.md)
- [Projection of a schedule of a composition onto its first component](sched-proj-left.md)
- [Projection of a schedule of a composition onto its second component](sched-proj-right.md)
- [Pasting schedules of the components of a composition](sched-of-proj.md)
- [Projection of a behaviour of a composition onto its first component](beh-proj-left.md)
- [Projection of a behaviour of a composition onto its second component](beh-proj-right.md)
- [Pasting behaviours of the components of a composition](beh-of-proj.md)

## Related topics

- [Labelled transition systems](../labelled-transition-systems/README.md): an I/O automaton is a labelled transition system with an action signature.
- [Calculus of communicating systems](../calculus-of-communicating-systems/README.md): CCS synchronizes two complementary actions into one internal step (a handshake between exactly two processes); in a composition of I/O automata an output synchronizes with every component that has it as an input and stays visible, hiding being a separate operation.
- [FLP impossibility](../../concurrent-systems-and-protocols/flp-impossibility/README.md): the asynchronous message-passing model of the FLP theorem, of the kind I/O automata were designed to describe.

## Sources

- N. A. Lynch, M. R. Tuttle, *An introduction to input/output automata*, CWI Quarterly 2(3), 1989, 219–246.

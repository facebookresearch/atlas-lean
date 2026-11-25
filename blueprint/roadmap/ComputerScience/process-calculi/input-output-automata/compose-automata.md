# Composition of I/O automata

Let $A_1$ and $A_2$ be [input/output automata](ioautomaton.md) with [strongly compatible](strongly-compatible.md) signatures. Their composition $A_1 \| A_2$ (Lynch and Tuttle, 1989, §3.2, for two automata) has as states the pairs of states, as start states the pairs of start states, and as signature the [composition of the two signatures](compose-signatures.md). Its transitions are $(s_1, s_2) \xrightarrow{a} (t_1, t_2)$ for an action $a$ of either component such that each component [moves](move-or-stay.md) from $s_i$ to $t_i$ on $a$: a component that has $a$ in its signature takes one of its transitions labelled $a$, and the other component stays unchanged. A shared action is therefore taken simultaneously by both components, which is how an output of one is received as an input by the other. The composition is again input-enabled.

**Relation to the source.** Lynch and Tuttle compose countable families; here two automata are composed. Composition does not hide the actions shared by the components: they remain external, an action that is an output of one component and an input of the other being an output of the composition, and an action that is an input of both an input, as in the source, where hiding is a separate operation.

## Background

- [Component move in a composition](move-or-stay.md): the transition of each component.
- [Strongly compatible signatures](strongly-compatible.md): the hypothesis that makes the composed signature a signature and the composition input-enabled.
- [Composition of action signatures](compose-signatures.md): the signature of the composition.

## Sources

- N. A. Lynch, M. R. Tuttle, *An introduction to input/output automata*, CWI Quarterly 2(3), 1989, 219–246: §3.2.

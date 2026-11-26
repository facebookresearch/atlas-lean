# Input/output automaton

An input/output automaton $A$ with actions in $\alpha$ and states in $\sigma$ consists of an [action signature](action-sig.md) $\mathrm{sig}(A)$ over $\alpha$, a nonempty set of start states and a labelled transition system on $\sigma$ with labels in $\alpha$, such that every transition is labelled by an action of $\mathrm{sig}(A)$ and $A$ is input-enabled: for every state $s$ and every input action $a$ there is a transition $s \xrightarrow{a} s'$ (Lynch and Tuttle, 1989, §3.1). Input-enabledness expresses that an automaton cannot block its environment: it controls only its outputs and internal actions.

**Relation to the source.** Lynch and Tuttle's automata also carry a partition of the locally controlled (output and internal) actions, used to define fair executions. The automata here have no such partition, so fairness does not arise.

## Background

- [Labelled transition systems](../labelled-transition-systems/README.md): the underlying structure.

## Sources

- N. A. Lynch, M. R. Tuttle, *An introduction to input/output automata*, CWI Quarterly 2(3), 1989, 219–246: §3.1.

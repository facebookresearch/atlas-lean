---
declaration: structure
origin: cited
statement: formalized
lean: Cslib.Automata.PDA
---

# PDA

A pushdown automaton over input alphabet `T`, with states in `σ` and
stack alphabet `Γ`. From state `q`, on optional input (`none` is an
`ε`-transition) and popped stack symbol `γ`, a transition chooses finitely
many pairs of a next state and a list of symbols to push.

This is the generalized model: the state and stack types themselves are
unrestricted, and only each transition is finitely branching. A standard
(textbook) pushdown automaton additionally has finite support in the sense
of `PDA.FinitelySupported`; without it, `PDA.accepts` can be an arbitrary
language, so the reverse PDA-to-CFG direction needs finiteness hypotheses.

## Depends on

This node has no prerequisites.

## Sources

- [CSLibExt, CSLibExt.Computability.Automata.PDA.Basic](../../../../../../sources/v2/CSLibExt.md)

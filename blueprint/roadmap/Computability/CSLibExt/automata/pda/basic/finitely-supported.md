---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Automata.PDA.FinitelySupported
---

# Finitely Supported

Finite support: some finite sets of states, stack symbols, and input
labels such that the start state and the initial stack symbol are
supported, transitions between supported states and stack symbols stay
within the support, and no transition from a supported configuration
consumes an unsupported input label. This is the finiteness condition of
a standard pushdown automaton; computations from the initial
configuration then only ever visit finitely many states, push finitely
many stack symbols, and respond to finitely many input letters.

## Depends on

- [PDA](pda.md)

## Sources

- [CSLibExt, CSLibExt.Computability.Automata.PDA.Basic](../../../../../../sources/v2/CSLibExt.md)

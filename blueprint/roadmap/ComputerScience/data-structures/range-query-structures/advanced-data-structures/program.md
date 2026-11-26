# Deterministic cell-probe programs

A deterministic cell-probe program has `cells` addresses, word width `width` and result type
`α`. It is a finite tree with three node forms:

- A return leaf holds a value of type `α` and accesses no cells.
- A read holds an address in `Fin cells` and one continuation program for each possible word
  in `BitVec width`; the observed word chooses the branch.
- A write holds an address in `Fin cells`, a word in `BitVec width`, and a single continuation
  program. The old cell contents do not choose the continuation.

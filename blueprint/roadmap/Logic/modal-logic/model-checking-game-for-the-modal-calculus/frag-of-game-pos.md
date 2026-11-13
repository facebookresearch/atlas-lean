# Projection of game positions onto the fragment arena

A game position with empty binder
stack whose formula is the μ-calculus reading of a fixpoint-free formula $\varphi$, at world $w$,
is sent to the embedded position $(\varphi, w)$. Every other game position (one whose formula
contains a fixpoint operator or a variable, or one with a nonempty stack) is sent to the losing
state.

The losing state is a default that is never reached on plays that stay in the arena, since every
move from an embedded position lands on an embedded position.

## Sources

- C. Stirling, *Modal and Temporal Properties of Processes*, Springer 2001, Chapter 6.

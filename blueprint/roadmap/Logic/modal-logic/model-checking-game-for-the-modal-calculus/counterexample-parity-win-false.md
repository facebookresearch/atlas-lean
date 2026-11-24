# Verifier loses the infinite play of $\mu X.\, \nu Y.\, X$

Consider the infinite
sequence of positions of the model-checking game for $\mu X.\, \nu Y.\, X$ (with one-element
types of worlds and atoms) that starts at this formula with empty binder stack and repeats three
steps: unfold $\mu X$, unfold $\nu Y$, and follow the variable $X$ back to the formula with empty
stack. This play does not satisfy the parity condition: it is not the case that the least binder
priority occurring infinitely often is even.

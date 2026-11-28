# Exponentiation program

For a number of steps $m$, the exponentiation program is the generic-group program over two inputs given by the [exponentiation recursion](pow-prog-aux.md) with $m$ steps from accumulator index $0$ and base index $1$. The indices $0$ and $1$ are only the *initial* positions of the accumulator and the base: each step makes one multiplication query of the accumulator by the base and rebinds the accumulator to the answer, at the newest index, while the base keeps its position.

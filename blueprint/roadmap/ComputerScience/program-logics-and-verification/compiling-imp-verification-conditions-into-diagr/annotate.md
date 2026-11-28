# Annotating a compiled diagram

For an annotated command $c$ and a postcondition $Q$, the result is an annotation of the compiled diagram of the command without its annotations, `compile c.strip`, for $Q$. It is built structurally, placing the source generator's preconditions on the internal wires and retaining the supplied loop invariants on the feedback wires.

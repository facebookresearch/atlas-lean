# Pre

Compute the backward assertion `C.pre Q` for an annotated command
`C` and heap postcondition `Q`. If `C.vc Q` holds, `C.pre Q` is sufficient
for safe partial correctness. Atomic commands use the
lookup, ownership, update and universal fresh-allocation conditions; sequences
nest these assertions and conditionals select by the guard. Loops return the
supplied invariant. A frame returns `body.pre localPost ⋆ R`; its obligations
connect that local postcondition to the requested result.

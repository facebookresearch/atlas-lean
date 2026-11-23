# Pre

Compute the backward assertion `C.pre Q` for an annotated command
`C` and heap postcondition `Q`. It is sufficient for safe partial correctness
only when the separate obligations `C.vc Q` hold. Atomic commands use the
lookup, ownership, update and universal fresh-allocation conditions; sequences
nest these assertions and conditionals select by the guard. Loops return the
supplied invariant. A frame returns `body.pre localPost ⋆ R`; its obligations
connect that local postcondition to the requested result.

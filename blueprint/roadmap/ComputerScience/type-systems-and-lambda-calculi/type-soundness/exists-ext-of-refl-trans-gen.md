# Multi-step preservation with growing worlds

Let `ext` be a preorder on worlds and
`HasType w s A` a typing predicate that depends on a world `w`. If every step from a state of
type `A` in world `w` reaches a state of type `A` in some world extending `w`, then every state
reachable from a state of type `A` in `w` has type `A` in some world extending `w`.

## Sources

- Sewell, *Semantics of Programming Languages*, Theorem 24; Pierce, *Types and Programming Languages*, Theorem 13.5.3.

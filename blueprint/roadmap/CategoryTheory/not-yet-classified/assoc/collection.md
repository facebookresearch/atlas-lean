# Collection

The associative symmetric collection.

At a finite type `I`, `collection.obj` is `LinearOrder I`. For
`e : I ≃ J` extracted from the `Core FintypeCat` morphism, the map
sends `ord : LinearOrder I` to `e.symm.linearOrder` on `J`, so
`x ≤ y` in `J` iff `e.symm x ≤ e.symm y` in `I`.

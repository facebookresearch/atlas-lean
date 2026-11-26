# Orientable

Some choice of face reversals makes the mesh `ConsistentlyOriented`. For a mesh with
`ClosedSurface` this is orientability of the closed surface it describes. On a raw mesh it is only
the edge-parity condition: a mesh with a boundary edge is never orientable in this sense (a single
triangle is not), and `Valid` faces are not required (the one face `[0, 1]` uses both directions
of its edge and passes).

# Orientability

Some choice of face reversals makes the mesh `ConsistentlyOriented`. For a
mesh with `ClosedSurface` this is orientability of the closed surface it describes. On a raw mesh
it is only the edge-parity condition, which fails when a face uses a directed edge whose reverse no
face uses. One face may supply both directions of an edge: the single face `[0, 1]` is orientable.
`Valid` faces never do, so in a `Valid` orientable mesh every edge lies in a second face
(`Orientable.edge_shared_of_valid`), and a boundary edge rules orientability out.

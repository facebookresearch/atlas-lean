# Link degree

The number of entries of `linkEdgesList M v` that contain `u`. Each corner
of a face at `v` contributes one entry, the edge joining the corner's two neighbors, so a loop
`s(u, u)`, which only a face with a repeated vertex produces, counts once rather than twice.
`Valid` faces produce no loops, so on the meshes `ClosedSurface` accepts this is the degree of `u`
in the link of `v`, counted with multiplicity.

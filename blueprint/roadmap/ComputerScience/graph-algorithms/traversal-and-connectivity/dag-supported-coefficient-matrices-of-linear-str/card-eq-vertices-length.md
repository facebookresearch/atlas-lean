# Card eq vertices length

The Fintype carrier has exactly the enumerated vertices: `vertices_nodup`
and `vertices_complete` identify `Finset.univ` with `g.vertices.toFinset`,
so `Fintype.card V = g.vertices.length` (`Finset.card` of a nodup list).

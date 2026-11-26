# Consistently Oriented

Every directed edge is used by at most one face, and its reverse by some face. For a mesh
with `ClosedSurface` this says the faces are coherently oriented: the two faces at each edge
traverse it in opposite directions. On a raw mesh it is only this edge condition: a boundary edge,
used in one direction only, makes it fail, and the faces need not be valid polygons.

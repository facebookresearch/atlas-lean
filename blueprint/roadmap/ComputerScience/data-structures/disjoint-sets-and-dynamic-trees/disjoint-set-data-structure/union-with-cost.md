# Union in a parent forest with cost

For a parent forest $F$ and vertices $x$ and $y$, the
costed union returns the union of $x$ and $y$ in $F$ together with a cost equal to the cost of
finding the root of $x$ plus the cost of finding the root of $y$ (each one unit per visited
vertex, including the root), plus one more unit when the roots of $x$ and $y$ are distinct; when
they coincide, union performs no link and none is charged.

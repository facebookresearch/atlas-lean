# Trees of triangles

The trees of triangles on a vertex set $V$ are the graphs on $V$
built recursively as follows. A graph whose edges are exactly the three edges of a triangle on
distinct vertices $a, b, c$ is a tree of triangles. If $H_0$ is a tree of triangles, $xy$ is an
edge of $H_0$, and $z$ is a vertex different from $x$ and $y$ with no neighbours in $H_0$, then
the graph obtained from $H_0$ by joining $z$ to $x$ and to $y$ is a tree of triangles.

## Sources

- AIM-COMBINATORICS-0056, aim-combinatorics-notes.json notes[55]: any graph built recursively by starting with a triangle, and then adding two edges at a time that forms a single new triangle with an existing edge.

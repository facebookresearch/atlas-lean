# Paths of adjacent steps between two points

For an adjacency relation and a distance $d$ on a set, a path from $x$ to $z$ is defined inductively: either $x = z$, or $x$ is adjacent to some $y$ with $d(x, z) = d(x, y) + d(y, z)$ and there is a path from $y$ to $z$. So the distance adds along the adjacent steps of the path.

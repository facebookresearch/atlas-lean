# A convex vertex of a monotone mountain cuts off an ear

A *monotone mountain* is a simple polygon $P = p_0 p_1 \cdots p_{n-1}$ whose vertices have strictly increasing $x$-coordinates, $x(p_0) < x(p_1) < \dots < x(p_{n-1})$, so that its boundary consists of the $x$-monotone chain $p_0 p_1 \cdots p_{n-1}$ and the edge $p_{n-1} p_0$, the *base*. Suppose $n \ge 4$ and all vertices other than $p_0$ and $p_{n-1}$ lie strictly above the line through the base. Then some vertex $p_i$ with $0 < i < n - 1$ is *convex*, meaning that its interior angle is less than $\pi$ (for example the leftmost of the vertices farthest from the base), and for every such convex vertex the segment $p_{i-1} p_{i+1}$ is an interior diagonal of $P$.

## Depends on

- [Diagonals and triangulations of a simple polygon](diagonals-and-triangulations-of-a-simple-polygon.md)

## Sources

- J. Erickson, *Computational Topology*, lecture notes, University of Illinois, 2023, Chapter 1 (Simple polygons), <https://jeffe.cs.illinois.edu/teaching/comptop/2023/notes/01-simple-polygons.pdf>: Section 1.4, proof of the Diagonal Lemma (the definition of a monotone mountain, here made precise by the strictly increasing $x$-coordinates): every monotone mountain has a convex vertex $p_i$ other than $p_0$ and $p_{n-1}$, and for any such vertex $p_{i-1} p_{i+1}$ is a diagonal

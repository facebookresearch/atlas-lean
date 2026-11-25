# Construction of the vertical cell decomposition of a polygonal free space

The connectivity theorem for a supplied vertical cell decomposition (two free points are joined in the free space if and only
if their cells are connected in the incidence graph) and the polygonal workspace are separate results and definitions and are
not part of this node. This node collects only the remaining clauses.

## Expansion

A sound expansion has separate pages for:

1. **Construction.** For a bounded workspace with an outer simple polygon and disjoint closed simple holes, $n$ vertices in total and
   distinct $x$-coordinates, the vertical decomposition exists, with a uniform $O(n)$ bound on the number of trapezoids plus walls.
2. **Whole-plane coverage,** by a stated reduction of the unbounded case to the bounded one, or by unbounded trapezoids and walls.
3. **Sweep algorithm,** computing the decomposition in $O(n \log n)$ time, as an algorithmic statement.

## Sources

- Planning Algorithms, Chapter 6: Combinatorial Motion Planning — S. M. LaValle, Cambridge University Press, 2006. <http://msl.cs.uiuc.edu/~lavalle/planning/ch6.pdf> Sec. 6.2.2: the vertical cell decomposition of a polygonal free space and its computation in $O(n \lg n)$ time by plane sweep.

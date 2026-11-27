# Hill formula for the ordinary crossing number of complete graphs

For every integer $n\ge3$, the infimum in the naturals of crossing counts of admissible plane drawings of $K_n$ is

$$
\left\lfloor\frac{\lfloor n/2\rfloor\lfloor(n-1)/2\rfloor\lfloor(n-2)/2\rfloor\lfloor(n-3)/2\rfloor}{4}\right\rfloor.
$$

Use distinct vertex points and injective continuous edge paths, no interior hit on a vertex, a finite set of proper two-edge intersections (locally coordinate axes under a plane chart), and no triple interior intersections. Count spatial points, allowing multiple intersections of the same pair to contribute separately.

## Depends on

- Admissible continuous drawing and finite cardinality of the set of crossings; natural infimum over possible counts.

## Expansion

Separate the general ordinary-drawing normalization: for an admissible drawing, construct a polygonal, locally straight-crossing drawing with no adjacent crossings and no larger crossing count, with the same underlying graph. Then use the normalized odd-order lower bound and the even-order deletion step as parts of the complete-graph calculation.

## Proof outline

Show nonemptiness of the count set before passing from an infimum to the least count. Expose the two-page realizing construction and the lower-bound reduction as distinct prerequisites, keeping the natural arithmetic at $n=3$.

## Sources

- [Comparator statement: `OAI.Paper170.complete_graph_crossing_number`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CompleteCrossing.lean#L81-L84)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/165.md)
- [Proof of the reduction and the prerequisite interfaces](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/CompleteCrossing/Main.lean)

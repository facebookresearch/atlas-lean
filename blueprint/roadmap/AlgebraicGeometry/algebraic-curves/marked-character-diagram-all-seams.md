# Framed flag compatibility at every seam of the produced marked diagram

Take a proper surface-presentation diagram $D$ with finitely many vertices, a seam $q$ whose designated adjacent facet $\mathrm{facet}(q,\mathrm{none})$ has rank at least that of all facets, and assume the parent of its band cut has positive genus. Over a commutative coefficient ring $R$ and a field $K$ with a specified $R$-algebra structure, fix puncture data $P$, an existing $K$-valued solution $x$, and a boundary occurrence $(b_0,i_0)$ on the parent (a boundary index and an index in its length).

Apply the source’s based-circle gauge and handle transports to $x$, form the cut witness with its row and column ranks, and graft its band to obtain the marked diagram $C$. Its generator values $v$ are the based cut lifts of $x$ using the frames obtained from the old port frame and marked handle transport. For every seam $s$ in $C$, evaluate its left and right matrix expressions at $v$ over $K$ and use each resulting invertible matrix in the square matrix ring on the seam coordinates as a coordinate-frame isomorphism. With the seam grade $a$ on coordinates, their two frames yield the same prefix subspaces at every grade and the same grade-$k$ coordinate projection on the common prefix of grade $<k+1$, for every $k$. This imposes the graded maps as well as the underlying flags; it quantifies over all produced seams, not only the first short one.

## Depends on

- Diagram incidence, properness, parent genus, marked band grafting, generator lifts and graded frames as defined by the source construction.

## Proof depends on

- Seam-by-seam transport identities for the generated values and separate old-seam and new short-seam flag arguments.

## Expansion

Pin the produced diagram and lift from the cited ProducedDiagram and ProducedEquations modules rather than existentially choosing a replacement that satisfies the seam equations. Decompose over the original seam and all short-seam types; prove the prefix and graded-projection equalities on each. Neither integral-point existence nor density follows from this endpoint alone.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CharacterVarietiesAllSeamsSupport.lean#L17-L20), [marked diagram and generator lifts](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/AlgebraicGeometry/CharacterVarieties/Seams/ProducedDiagram.lean#L14-L61), and [framed flag equations](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/AlgebraicGeometry/CharacterVarieties/Seams/ProducedEquations.lean#L16-L31).

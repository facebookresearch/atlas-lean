# A 116-generator Artin group without a geometric CAT(0) action

Index the generators by $0,\ldots,115$. For $b=0,1,2$, form a chain of 39 positions whose first two letters are $b$ and $(b+1)\bmod3$, while position $i$ for $2\le i\le38$ has letter $5+37b+(i-2)$. The Coxeter matrix has diagonal $1$, label $3$ for a pair adjacent in some chain, label $2$ for remaining pairs at least two positions apart in a common chain or with one letter in $\{3,4\}$ and the other in $\{0,1,2\}$, and infinite label otherwise. It is symmetric and has only $2,3,\infty$ off the diagonal.

The associated Artin group has no isometric, proper, cocompact action on any nonempty proper CAT(0) space. CAT(0) here includes existence of constant-speed segments and Euclidean squared-distance comparison for every pair of segments from a common vertex. Proper means finitely many translates of any compact set meet that set; cocompact means the translates of one compact set exhaust the space.

## Depends on

- [Artin group presentation](artin-group.md)
- [CAT(0) four-point comparison](../../../../Geometry/metric-geometry/cat-0-spaces/is-cat0-four-point.md)
- Translate this finite matrix to the existing zero-label-for-infinity convention; compare the segment comparison definition of CAT(0) with the available four-point model.

## Proof depends on

- Derive the obstruction from the specific chain overlaps and the two sentinel letters.

## Expansion

Verify the 116 labels and overlap priority first. Use the existing Artin presentation after checking unused diagonal relations are trivial. Then formalize the obstruction in the nonempty proper geodesic metric model.

## Sources

- OpenAI Math, [`main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ArtinCAT0.lean#L65-L74) (statement and local definitions).

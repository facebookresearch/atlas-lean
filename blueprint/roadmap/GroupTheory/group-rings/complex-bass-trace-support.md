# Support of the complex Hattori–Stallings trace

Let $G$ be any discrete group and $R=\mathbb C[G]$. On the Grothendieck group of finitely generated projective right $R$-modules (isomorphism and direct-sum relations), take the Hattori–Stallings trace with values in finitely supported complex functions on conjugacy classes. For a module split off a finite free right module, form the idempotent projecting onto it, sum the diagonal entries and sum coefficients in each conjugacy class; extend additively to virtual classes. For every virtual class this trace is zero on each conjugacy class represented by an infinite-order element, and its support is contained in the classes represented by finite-order elements. There is no amenability hypothesis or analytic $K$-theory completion.

## Depends on

- Projective right-module $K_0$, idempotent presentations and conjugacy-class coefficient sums.

## Proof depends on

- Trace well-defined under different splittings and direct sums, and the vanishing theorem on infinite-order classes for arbitrary groups.

## Expansion

Construct the map on virtual module classes via the matrix idempotent quotient, verify that rectangular products have the same class trace in either order, and separate the general vanishing argument from its support reformulation.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BassTrace.lean#L470-L476) and [its definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BassTrace.lean).

# Universal hyperreflexivity with an explicit bound

In any complete complex Hilbert space $H$, for every von Neumann algebra $M\subseteq\mathcal B(H)$ and operator $T$, the operator-norm distance from $T$ to $M$ is at most $2C\sup_e\|(1-e)Te\|$, over self-adjoint idempotents $e$ in the commutant of $M$. The explicit constant is given by $R=4\sqrt2$, $L=(1+4R)^2$, $K=6\pi^2(1+4L)$, $F=\max(3K+2,1+2R,2)$ and $C=3F+2$.

## Depends on
The concrete commutant projections, the displayed projection supremum, and distance as an infimum of norms of differences.

## Proof depends on

- [Universal amplified commutator estimate](uniform-matrix-commutator-bound.md).

The amplified bound at the displayed $C$, and the operator-distance comparison with the completely bounded norm of the restricted derivation on the commutant.

## Expansion

Separate the explicit row, cyclic, corner and factor bookkeeping that yields this $C$ from the distance formula. In the latter step relate the scalar derivation norm on the commutant to the projection off-diagonal supremum. An unspecified existential constant does not give the numerical assertion.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/KadisonSimilarity.lean#L110-L113) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/288.md).

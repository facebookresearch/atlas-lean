# Summability of critical honeycomb bridge lengths in a strip and corridor

For each integer $h\ge1$ take honeycomb strip paths from $U_{0,0}$ to any $D_{i,h-1}$, with adjacency and strip indices as in the [strip mass result](critical-honeycomb-strip-mass-and-displacement.md), and no repeated vertices. For a path $P$ of $\ell(P)$ listed vertices put $w(P)=(2\cos(\pi/8))^{-\ell(P)}$. The confined class requires each vertex's horizontal coordinate to have absolute value at most $h(\log h)^2$, using $x(U_{i,j})=i+j/2$ and $x(D_{i,j})=i+j/2+1/2$. On each of the free and confined classes the three series with terms $w(P)$, $\ell(P)w(P)$ and $\ell(P)w(P)/\sum_{P'}w(P')$ respectively are summable, with mass from the same class. The normalized series uses real division with $x/0=0$; this does not claim a nonempty corridor at $h=1$.

## Depends on

- Strict strip bridge lists, their absolute horizontal corridor, and mass normalization by class.

## Proof outline

Give an exponential tail or corresponding first-moment summability lemma at fixed h. Check $h=1$ with width zero and preserve the totalized normalized sum, not a conditional probability law that assumes positive mass.

- Strip-size-dependent summability of the length-weighted series, then restriction and scalar division for the confined and normalized ones.

## Sources

- [Comparator statement: `OAI.PolynomialVacuumBridge.Corridor.finite_bridge_sums`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/HoneycombBridgeFiniteness.lean#L60-L62)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/237.md)

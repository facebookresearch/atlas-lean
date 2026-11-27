# Adaptive value-and-gradient sampling of a normalized Gibbs law

An admissible potential is $C^2$, has value and gradient zero at the origin, and has Hessian quadratic forms between identity and twice identity. The target is the density $e^{-V}$ normalized with respect to Euclidean volume. A query at $x$ returns the ordered pair $(V(x),\nabla V(x))$. With budget $q$ an algorithm consists of the seed probability space, measurable functions giving the next point from the seed and prior transcript, and a measurable terminal output function. A finite transcript starts padded with zero pairs, then each query fills its own slot. Use one uniform algorithm for every admissible potential. Feasibility requires each run measurable and total variation (supremum of event-probability differences) from the target at most $1/10$. The complexity is the infimum over feasible natural budgets in extended naturals.

## Sources

- [Pinned source definition](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/LogConcaveQuery.lean#L12-L72)

# Uniform near-identity unitary conjugacy for close von Neumann algebras

For every real $\varepsilon>0$ there is $\delta>0$ such that on every complete complex Hilbert space $H$, if the norm Hausdorff distance between the closed operator-norm unit balls of two unital von Neumann subalgebras $M,N\subseteq\mathcal B(H)$ is strictly less than $\delta$, then there exists a unitary $u$ with $uMu^*=N$ and $\|u-1\|<\varepsilon$. The same $\delta$ works over all spaces and representations.

## Depends on
Closed norm unit balls, their Hausdorff metric in the common operator algebra, and surjective unitary conjugacy as equality of the represented subalgebras.

## Proof depends on
Uniform perturbation estimates giving a near-identity spatial intertwiner, not just an abstract isomorphism or a one-sided near inclusion.

## Expansion
Separate the near-inclusion comparison, production of a common intertwiner, and a polar-decomposition step preserving the small distance from the identity. Check the direction and strictness of both tolerances.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/StrongKadisonKastler.lean#L37-L39) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/289.md).

# Single generation of finite diffuse factors with separable predual

Let $M\subset B(H)$ be a unital weak-operator-closed complex star subalgebra of the bounded operators on a complex Hilbert space. Assume $0\ne1$, its center consists of scalars, each isometry in $M$ is unitary, and every nonzero projection $p$ in $M$ has a proper nonzero subprojection $q$ (so $pq=qp=q$). Assume some same-universe separable complex Banach space has continuous dual conjugate-linearly isometrically equivalent to $M$, with its operator norm. Then there is $x\in M$ for which the intersection of all weak-operator-closed unital star subalgebras containing $x$ is $M$. No separability of $H$ or of the normed algebra is assumed.

## Depends on

- [Generated concrete von Neumann algebra](../../not-yet-classified/generated/generated-by.md).
- The scalar-center, finite, diffuse and conjugate-dual conditions above.

## Proof depends on

- A generator construction for arbitrary concrete finite diffuse factors with separable predual.

## Expansion

Bridge the weak-operator intersection to the double-commutant API and the conjugate-linear dual convention to the predual used by the proof. Separate the generator construction from verification that it generates the supplied concrete algebra, without replacing the hypothesis by norm separability.

## Sources

- OpenAI, [FactorGeneration comparator, single_generation_of_II1_separable_predual](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/FactorGeneration.lean#L41-L45).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/296.md).

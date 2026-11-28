# An invertible group-ring operator with Fuglede–Kadison determinant below one

There exist a finitely generated group $G$, $n\ge1$, and an $n\times n$ matrix $A$ over $\mathbb Z[G]$ whose scalar extension to $\mathbb Q[G]$ is a unit. Its bounded left-regular operator $T$ on $\ell^2(\{0,\ldots,n-1\}\times G)$ is invertible, with $(T\xi)_{i,h}=\sum_{j,g}A_{ij,g}\xi_{j,g^{-1}h}$. If $e_i$ is the unit vector at $(i,1)$, then

$$0<\exp\!\left(\frac12\operatorname{Re}\sum_i\langle e_i,\log(T^*T)e_i\rangle\right)<1.$$

The logarithm uses continuous functional calculus; the trace is not divided by $n$.

## Depends on

- Left-regular bounded group-ring representation and the specified continuous-functional-calculus determinant.

## Proof depends on

- [Characteristic-two one-sided inverse pair](../../../GroupTheory/group-rings/characteristic-two-direct-finiteness-counterexample.md) and its companion-matrix transfer with an exact trace estimate.

## Expansion

Prove the companion transfer separately: scalar extension must be a rational group-ring unit, not only an invertible Hilbert operator. Then verify the precise unnormalized trace inequality.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GroupRingDeterminant.lean#L52-L54) and [its definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GroupRingDeterminant.lean).

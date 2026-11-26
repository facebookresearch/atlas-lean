# A metric-entropy duality counterexample for the cube

For every $a,b\ge1$ there exist a positive integer $n$ and a compact origin-symmetric convex set $K\subset\mathbb R^n$ with nonempty interior. Put $Q=[-1,1]^n$ and $A^\circ=\{y:x\cdot y\le1\text{ for all }x\in A\}$. For sets $A,B$ let $N(A,B)$ be the least number of translates of $B$ covering $A$, with centers arbitrary in $\mathbb R^n$. Require actual finite covers of $K$ by translates of $Q$ and of $Q^\circ$ by translates of $a^{-1}K^\circ$. Then

$$b\log N(Q^\circ,a^{-1}K^\circ)<\log N(K,Q).$$

No asymptotic sequence of witnesses or limit is asserted in this endpoint.

## Depends on

- Ordinary real polarity and finite translate covers with the minimum over natural counts.

## Proof depends on

- Simultaneous finite cover witnesses and the strict gap between the two logarithmic entropies for arbitrary $a,b\ge1$.

## Expansion

Prove the upper cover estimate on the polar side and the lower bound on the primal side for the same symmetric convex body. Separate finite cover existence from numerical entropy bounds so no totalized infimum over an empty set certifies the strict inequality.

## Sources

- OpenAI, [MetricEntropyDuality comparator, exists_entropy_duality_counterexample_with_covers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MetricEntropyDuality.lean#L45-L54).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/329.md).

# Fixed-base exponential bound for uniform sunflowers

For every integer $r\ge3$ there is an integer $C\ge1$ such that for every integer $k\ge0$, every ground type, and every finite family $\mathcal F$ of distinct finite sets of exactly $k$ elements, if $|\mathcal F|>C^k$ then a subfamily of exactly $r$ members has a common pairwise intersection. More precisely, there are $\mathcal G\subseteq\mathcal F$ and a finite set $K$ with $|\mathcal G|=r$ and $A\cap B=K$ for all distinct $A,B\in\mathcal G$. The base $C$ depends on $r$ only, not on $k$ or the ground type. The threshold is strict.

## Depends on

- [Delta systems](is-delta-system.md), with exactly $r$ petals in the subfamily.

## Proof approach

The source transfers a bound on sunflower-free finite word families to uniform set families. The classical Erdős–Rado threshold is $k!(r-1)^k$, which cannot be bounded by $C^k$ with constant $C$ as $k$ grows. For $k=0$ there is at most one distinct empty set and the strict premise cannot hold. No explicit growth rate for $C$ as a function of $r$ is asserted.

## Related topics

- This bound is the uniform fixed-base form of the Erdős–Rado sunflower conjecture. The [Alweiss–Lovett–Wu–Zhang bound](theorem-1-4.md) has a different dependence on the uniformity.

## Sources

- OpenAI, [`erdosRadoSunflower`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/Sunflower.lean#L11-L18).

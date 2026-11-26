# Bounded approximation obstructions for discrete Lipschitz-free spaces

For a pointed metric space $(M,o)$, let $\operatorname{Lip}_0(M)$ be the real Lipschitz functions vanishing at $o$, normed by the supremum of absolute slopes over distinct pairs. Its real free space is the norm-closed linear span of evaluations $\delta_x:f\mapsto f(x)$ in the continuous dual. The approximation property requires that for every compact set $K$ and $\epsilon>0$ a bounded finite-rank real-linear operator approximate the identity with errors bounded on $K$ by a common $\eta<\epsilon$; its $\Lambda$-bounded form also requires operator norm at most $\Lambda$.

1. For each integer $p\ge1$ there is a countable pointed metric space with every distinct pair at distance at least one and all distances at most $B_p=300p^2+150p+5$. There is a finite set $A$ containing $o$ such that every operator $T$ of finite rank and norm at most $p$ on this free space has $\|T\delta_x-\delta_x\|\ge1/2$ for some $x\in A$.
2. There is a countable pointed metric space with every distinct pair at distance at least one, unbounded and not proper, whose free space has the approximation property but not its $\Lambda$-bounded form for any real $\Lambda\ge1$.

## Depends on

- [The approximation property](has-approximation-property.md) and the pointed Lipschitz/evaluation model above.

## Proof depends on

- Quantitative block construction at each $p$, a countable assembly preserving the evaluation obstructions, and compact-set approximation on that assembly.

## Expansion

Split the independently quantified block and assembled-space assertions when developing them. Verify quantitative finite evaluation obstructions before passing to the countable space, and distinguish the unbounded/properness conditions from uniform discreteness.

## Sources

- OpenAI, [DiscreteLipschitzFree comparator, source_endpoints](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/DiscreteLipschitzFree.lean#L156-L158).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/330.md).

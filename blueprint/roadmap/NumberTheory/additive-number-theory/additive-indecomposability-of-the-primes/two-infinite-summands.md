# No eventual prime sumset with two infinite summands

Let $A,B\subseteq\mathbb N$ each be infinite, with $0$ allowed in either. There is no natural
cutoff $N$ such that for every $n\ge N$, $n$ is in $A+B=\{a+b:a\in A,\ b\in B\}$ if and only if
$n$ is prime.

## Proof depends on

- [Log-free zero-density estimates](../../zeta-l-functions/dirichlet-l-functions/zeros-of-dirichlet-l-functions/log-free-zero-density-estimate.md)

## Expansion

Decompose the complex-character zero-density estimate for the smoothed prime supply in the moving residue classes and the combinatorial exclusion for two infinite summands. Check that the zero-density statements used control the actual family and smoothing ranges, not just individual characters.

## Sources

- [OstmannComplete.lean — `twoInfiniteSummandsImpossible`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/OstmannComplete.lean#L33-L35)

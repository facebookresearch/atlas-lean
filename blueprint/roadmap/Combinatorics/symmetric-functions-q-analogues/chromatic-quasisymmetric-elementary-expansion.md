# Elementary expansion for natural unit interval graph colorings

Let $h:\{0,\ldots,n-1\}\to\{0,\ldots,n-1\}$ be nondecreasing with $i\le h(i)$; join $i<j$ when $j\le h(i)$. For each finite number $r$ of variables let $X_{G,r}$ be the polynomial over $\mathbb N[q]$ summing $q^{a(f)}\prod_i x_{f(i)}$ over proper colorings $f$ by those $r$ colors, where $a(f)$ counts edges $i<j$ with $f(i)<f(j)$. There exists a map $\theta_G$ from the permitted permutations to partitions of $n$ such that, for **every** $r$,

$$
X_{G,r}=\sum_\sigma q^{\operatorname{inv}_G(\sigma)}e_{\theta_G(\sigma)}.
$$

The sum is over vertex permutations whose every adjacent descending pair is an edge; graph inversions are all inverted position pairs whose underlying vertices form an edge. The elementary product $e_\lambda$ is indexed by a partition of $n$. A single map works for all $r$, including $r=0$; it is not required to arise from a particular ordering of candidate tables.

## Depends on

- Natural unit interval graph, ordered proper-colouring ascents, permitted permutations and the elementary polynomial indexed by a partition.

## Proof outline

The comparator's `PermutationWitness` couples one map with its identity for all $r$. A finite table search can provide a witness if existence and its guarantee for all $r$ are verified. The result does not prescribe a selection rule.

- Construct one partition-valued map on the permitted permutations and verify all finite-variable identities for that same map.

## Sources

- [Comparator statement: `OAI.elementaryPositivityExpansion`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ElementaryPositivity.lean#L53-L71)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/169.md)
- [Finite-search witness and its projection](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/Chromatic/Main.lean)

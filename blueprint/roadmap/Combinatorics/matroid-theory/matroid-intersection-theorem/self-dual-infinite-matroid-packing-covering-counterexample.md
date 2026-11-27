# Self-dual infinite matroids without a packing-covering partition

Let $D$ be the disjoint union over $m\ge0$ of the Boolean functions on $m$ bits and $E=\mathbb Z\times D$. The set $E$ is countably infinite and admits matroids $M_0,M_1$, both with ground set $E$ and $M_i^*=M_i$, such that no union of one independent set from each matroid is $E$. Also no disjoint partition $E=P\sqcup C$ has both of the following: disjoint sets $S_i\subseteq P$ spanning the restrictions $M_i|P$; and sets $I_i\subseteq C$ independent in $(M_i^*|C)^*$ with $I_0\cup I_1=C$. The latter is contraction onto the retained set $C$.

## Depends on

- [Packing and covering](infinite-matroid-packing-covering.md)
- Infinite matroid duality and restriction, spanning and independent sets, and packing/covering on complementary parts.

## Proof outline

Give the infinite construction and its self-duality separately from the two negative assertions. Compare the contraction convention with the pinned Mathlib API and do not assume finitarity.

- Construction of the self-dual pair, failure of full independent covering, and exclusion of every packing/covering partition.

## Sources

- [Comparator statement: `OAI.InfiniteMatroidCounterexample.main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/InfiniteMatroid.lean#L23-L31)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/185.md)

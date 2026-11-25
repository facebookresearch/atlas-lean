# Counting $t$-subsets with a prescribed inside and outside

Let $\alpha$ be a finite set with $n$ elements, $A, B \subseteq \alpha$ disjoint and $t \in \mathbb{N}$ with $|A| \le t$. The number of $t$-element subsets $S \subseteq \alpha$ with $A \subseteq S$ and $S \cap B = \emptyset$ is

$$\binom{n - |A| - |B|}{t - |A|}.$$

The hypothesis $|A| \le t$ is needed: without it the count is $0$ while the right-hand side, with truncated subtraction $t - |A| = 0$, need not be; see the [general count](card-powerset-card-filter-subset-disjoin-2.md).

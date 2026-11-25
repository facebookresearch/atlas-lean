# MinHash collision probability

Let $U$ be a finite linearly ordered set and $A, B \subseteq U$ with $A \cup B \neq \emptyset$, and let $h_\pi(A) = \min \pi(A)$ denote the [min-hash](min-hash.md) of $A$ under a permutation $\pi$ of $U$. For a permutation $\pi$ drawn uniformly at random from the permutations of $U$ (for any $\sigma$-algebra on them in which singletons are measurable),

$$\Pr\big[h_\pi(A) = h_\pi(B)\big] = \frac{|A \cap B|}{|A \cup B|},$$

the Jaccard similarity of $A$ and $B$ (Broder, 1997).

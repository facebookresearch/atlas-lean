# MinHash, counting form

Let $U$ be a finite linearly ordered set and $A, B \subseteq U$ with $A \cup B \neq \emptyset$, and let $h_\pi(A) = \min \pi(A)$ denote the [min-hash](min-hash.md) of $A$ under a permutation $\pi$ of $U$. Then

$$\#\{\pi : h_\pi(A) = h_\pi(B)\} \cdot |A \cup B| = |A \cap B| \cdot |U|!,$$

where $\pi$ ranges over the $|U|!$ permutations of $U$.

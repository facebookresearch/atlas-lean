# Binary equal-length edit-distance distortion lower bound

For a finite set $W$ of binary words, $d_E$ is the minimum number of unit insertions, deletions and substitutions between words, without any cap on intermediate lengths. Let $c_1(W)$ be the infimum over injective $f:W\to\ell_1(\mathbb N;\mathbb R)$ of the product of the maximum of $\|f(x)-f(y)\|_1/d_E(x,y)$ and the maximum reciprocal over all distinct $x,y\in W$. There are $c>0$ and $d_0$ such that for every integer $d\ge d_0$ there is a finite $W$ containing at least two binary words of one common length $1\le n\le d$, with

$$
c_1(W)\ge\exp(c\sqrt{\log d\,\log\log d}).
$$

## Depends on

- [Unit-cost edit distance](edit-distance.md)
- Distortion on the inherited finite metric, measured in the full real sequence space ℓ₁.

## Expansion

Separate the fixed-length binary coding transfer. For every sufficiently large natural $M$ and every finite alphabet $\Gamma$ with $1\le |\Gamma|\le M$, choose one code $c$ assigning a binary block of length $M^2$ to each symbol, before choosing the input words. Concatenating the blocks gives $\operatorname{enc}_c(x)$ of length $M^3$ for every length-$M$ word $x$. For all length-$M$ words $x,y$, including $x=y$, the bounds are

$$
\frac{M^2}{804}\,d_E(x,y)\le d_E(\operatorname{enc}_c(x),\operatorname{enc}_c(y))\le M^2\,d_E(x,y).
$$

Keep the finite metric obstruction and the choice of length cap in the final application.

## Proof outline

State the obstruction for the tree/torus construction before coding. Prove the coding distance comparison and the parameter conversion giving a witness for every large cap, not just a subsequence. The tree-based comparator's length $n\le d$ already forces $n\ge1$ because there are at least two distinct equal-length words.

## Sources

- [Comparator statement: `OAI.TreeEdit.binary_lower_bound`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BinaryEditLower.lean#L49-L57)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/099.md)
- [Equivalent tree-based comparator endpoint (length-zero excluded by cardinality)](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/TreeEdit.lean)
- [Equivalent binary-torus statement on equal-length lists](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/TreeEdit.lean#L46-L48).
- [Fixed-length binary conversion](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/BinaryEdit/FixedLengthBinaryConversion.lean#L15-L29); [its use in the binary lower bound](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/BinaryEdit/BinaryLowerBound.lean)
- [Proof of the reduction and the prerequisite interfaces](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/TreeEdit/TorusLowerBound.lean)

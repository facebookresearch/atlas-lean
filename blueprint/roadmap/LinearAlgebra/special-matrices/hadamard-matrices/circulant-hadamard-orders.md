# Orders of real circulant Hadamard matrices

Let $n$ be a positive integer. There is a real $n\times n$ matrix $H$ with entries in $\{-1,1\}$, with $HH^{\mathsf T}=nI_n$, and with $H_{ij}=h(j-i)$ for some $h\colon\mathbb Z/n\mathbb Z\to\mathbb R$ and all $i,j\in\mathbb Z/n\mathbb Z$, if and only if $n=1$ or $n=4$. The entire matrix is circulant, not just the submatrix obtained by deleting a row and column.

## Depends on

- [Hadamard matrix](is-hadamard-matrix.md): use the real sign-matrix and row-Gram form of this condition. The generator convention $h(j-i)$ is equivalent to the opposite circulant convention after precomposing $h$ with negation.

## Proof depends on

- Positive square-order and two-adic reductions to $n=4u^2$ with $u$ odd when $n>1$.
- The cyclic-polynomial and local cyclotomic comparison ruling out $u>1$ for odd $u$; it is not the existence theorem for a bordered circulant core.

## Expansion

First identify the Gram entries with periodic autocorrelations, transport the signs to integer coefficients, and prove the order reduction. For the exclusion, isolate the binary coefficient decomposition and its local norm and residue comparisons; prove that their constraints contradict the sign autocorrelations for odd $u>1$. For the reverse implication, the length-one generator is $(1)$; for length four use $(-1,1,1,1)$, whose three off-peak periodic autocorrelations vanish.

## Sources

- OpenAI, [Circulant Hadamard comparator](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CirculantHadamard.lean#L13-L27) and [order reduction and final exclusion](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/LinearAlgebra/CirculantHadamard/Main.lean#L17-L32).

# Possible positive even Barker lengths

Let $n>0$ be even and $h_0,\ldots,h_{n-1}\in\{-1,1\}$ be integers. If $\left|\sum_{j=0}^{n-k-1}h_jh_{j+k}\right|\le1$ for each $0<k<n$, then $n=2$ or $n=4$. Products in this hypothesis do not wrap around the ends. No classification of odd lengths is included.

## Depends on

- Finite sign sequences and aperiodic (non-wrapping) autocorrelation.

## Proof depends on

- [Classification of real circulant Hadamard orders](../../LinearAlgebra/special-matrices/hadamard-matrices/circulant-hadamard-orders.md) and the cyclic-autocorrelation reduction for even lengths above two.

## Expansion

Use parity and the wraparound identity decomposing a periodic correlation into two aperiodic ones. For $n>2$, first prove $4\mid n$, then use the congruence modulo four and the correlation bound to force off-peak periodic terms to vanish. Build the real circulant Gram matrix and apply the classification.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EvenBarker.lean#L21-L24) and [its definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EvenBarker.lean).

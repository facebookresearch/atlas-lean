# κ-wise transfer through a two-round unbalanced Feistel network

Let a two-round unbalanced Feistel bijection map a key to (bucket, auxiliary) coordinates, with first-round function a reduced double tabulation hash and second-round function drawn from a $\kappa$-wise independent family. If the first round is injective on a set of keys (which fails with probability at most a bound polynomially small in $n$ above the size threshold), then the bucket–auxiliary coordinates of any $\kappa$ distinct keys of that set are independent and uniform; consequently, with probability $1 - \delta$, the restriction of the bucket map to any $\kappa$ keys is within statistical distance $\delta$ of a $\kappa$-wise independent assignment.

## Proof sketch

On the injectivity event, distinct keys have distinct first-round outputs, and the second round's $\kappa$-wise independence makes the masked coordinates uniform and independent; the bijection carries this to the output coordinates. The failure event is bounded by the collision probability of the first round.

## Depends on

- [Universal key-quotienting permutation](../balls-to-slots-and-kick-trees/universal-key-quotienting-permutation.md)
- [k-wise independent hash family](../word-ram-hash-families/k-wise-independent-hash-family.md)

## Proof depends on

- [Thorup's high independence of double tabulation](../word-ram-hash-families/high-independence-of-double-tabulation.md)
- [Multiply-shift is 2/2^M-universal](../word-ram-hash-families/multiply-shift-is-universal.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul and M. Liu, "On the Optimal Time/Space Tradeoff for Hash Tables", Proceedings of the 54th ACM Symposium on Theory of Computing (STOC), 2022; arXiv:2111.00602.
- M. Thorup, "Simple Tabulation, Fast Expanders, Double Tabulation, and High Independence", Proceedings of the 54th IEEE Symposium on Foundations of Computer Science (FOCS), 2013; arXiv:1311.3121.
- M. Luby and C. Rackoff, "How to Construct Pseudorandom Permutations from Pseudorandom Functions", SIAM Journal on Computing 17(2), 1988.

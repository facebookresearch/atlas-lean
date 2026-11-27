# Word-parallel rank of packed fingerprints

Let $m$ fingerprints $k_0, \dots, k_{m-1} < 2^f$ be packed into one machine word in lanes of width $f + 2$ bits (one guard bit per lane), with $m (f + 2) \le w$ and $m < 2^{f+2}$. Then for a query $q < 2^f$ the count $|\{j < m : k_j < q\}|$ is computed by a constant number of word operations: replicate $q$ into every lane by multiplying with the all-lanes-one constant, subtract lane-wise from the packed word with the guard bits set (no borrow crosses lanes), mask the guard bits, and sum them by one more multiplication.

## Proof sketch

Setting each guard bit before subtracting makes each lane's difference nonnegative, so lanes do not borrow from their neighbours, and the guard bit of lane $j$ survives exactly when $k_j \ge q$. Multiplying the masked guard bits by the all-lanes-one constant accumulates their count in the top lane, which fits because $m < 2^{f+2}$.

## Depends on

- [The word-RAM model](../../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Sources

- M. L. Fredman and D. E. Willard, "Surpassing the Information Theoretic Bound with Fusion Trees", Journal of Computer and System Sciences 47(3), 1993.
- M. A. Bender, M. Farach-Colton, J. Kuszmaul and W. Kuszmaul, "Modern Hashing Made Simple", Proceedings of the 2024 SIAM Symposium on Simplicity in Algorithms (SOSA), 2024.

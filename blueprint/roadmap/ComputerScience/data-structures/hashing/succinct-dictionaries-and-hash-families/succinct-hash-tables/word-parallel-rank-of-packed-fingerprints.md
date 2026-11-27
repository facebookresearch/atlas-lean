# Word-parallel rank of packed fingerprints

Let $m$ fingerprints $k_0, \dots, k_{m-1} < 2^f$ be packed into one machine word in lanes of width $f + 2$ bits whose top bit is a guard bit, with $m (f + 2) \le w$ and $m < 2^{f+2}$. Then for a query $q < 2^f$ the count $|\{j < m : k_j < q\}|$ is computed by a constant number of word operations: replicate $q$ into every lane by multiplying with the all-lanes-one constant, subtract lane-wise from the packed word with the guard bits set (no borrow crosses lanes), mask the guard bits and shift them down to the low bit of their lanes, sum them by one more multiplication with the all-lanes-one constant, read the sum $s = |\{j : k_j \ge q\}|$ from the top lane, and return $m - s$.

## Proof sketch

Setting each guard bit before subtracting makes each lane's difference $2^{f+1} + k_j - q$ positive and below $2^{f+2}$, so lanes do not borrow from their neighbours, and the guard bit of lane $j$ survives exactly when $k_j \ge q$. Multiplying the shifted guard bits by the all-lanes-one constant leaves in lane $i$ the number of surviving guard bits in lanes $0, \dots, i$, at most $m < 2^{f+2}$, so no lane overflows and the top lane holds $s$.

## Depends on

- [The word-RAM model](../../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Sources

- M. L. Fredman and D. E. Willard, "Surpassing the Information Theoretic Bound with Fusion Trees", Journal of Computer and System Sciences 47(3), pp. 424-436, 1993.

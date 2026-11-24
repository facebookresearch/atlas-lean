# Winnowing: density 2/(w+1) and the lower bound for local fingerprinting

Let $h_1, h_2, \dots$ be the hashes of the consecutive $k$-grams of a document, where $k$ is the noise threshold, and let $w = t - k + 1$ for a guarantee threshold $t \ge k$. An algorithm is local if, for every window $h_i, \dots, h_{i+w-1}$ of $w$ consecutive hashes, it selects one of these hashes as a fingerprint and the choice depends only on the window's contents. Winnowing selects in each window the minimum hash, taking the rightmost occurrence in case of ties. Schleimer, Wilkerson and Aiken (2003) prove: any local algorithm finds every matching pair of substrings of length at least $t$ (Lemma 1); for independent uniformly distributed hashes, the density of winnowing, the expected fraction of hashes selected as fingerprints, is asymptotically $2/(w + 1)$ (Section 3.1); and every local algorithm with noise threshold $k$ and guarantee $t = w + k - 1$ has density at least $1.5/(w + 1)$ (Theorem 1), so winnowing is within $33\%$ of the lower bound. They conjecture that $2/(w + 1)$ is a lower bound for every local algorithm.

## Expansion

1. The model: $k$-gram hashes, windows of size $w$, local algorithms, and the noise and guarantee thresholds.
2. Lemma 1: a match of length at least $t$ contains a full window of hashes, and a local algorithm selects the same hash in both copies.
3. The density of winnowing: a charging argument in which a window is charged when it selects a hash not selected by the previous window, which happens when the minimum of the union of two consecutive windows lies at its leftmost or rightmost position, each with probability $1/(w + 1)$.
4. Theorem 1: the lower bound, using only pairs of windows far enough apart to be disjoint.
5. Comparison with the 0 mod $p$ selection method, whose density for comparable guarantees is larger, as a separate statement.

## Sources

- S. Schleimer, D. S. Wilkerson and A. Aiken, Winnowing: local algorithms for document fingerprinting, in *Proc. 2003 ACM SIGMOD International Conference on Management of Data*, 2003, 76–85, Definition 1, Section 3.1, Lemma 1 and Theorem 1. <https://doi.org/10.1145/872757.872770>

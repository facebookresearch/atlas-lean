# Subset-sum and random-matrix hashing are optimally Δ-universal

(Subset sums.) Let $G$ be a finite additive group (for example $(\mathbb{Z}/q)^m$ for any modulus $q \ge 1$) and let $w_1, \dots, w_n$ be independent uniform elements of $G$. Hash $x \in \{0,1\}^n$ to $H_w(x) = \sum_{i : x_i = 1} w_i$. For distinct $x \ne x'$ the difference $H_w(x) - H_w(x')$ is uniform on $G$, so the family is $1/|G|$-almost $\Delta$-universal and distinct words collide with probability exactly $1/|G|$. Hashing $r$ independent uniformly random binary rows with the same weights is within statistical distance $r$ times the single-row leftover-hash error of $r$ independent uniform outputs, jointly with the weights.

(Matrices.) Over a finite field $F$, a uniform $m \times n$ matrix $A$ maps every fixed nonzero vector to a uniform vector of $F^m$; hence $x \mapsto Ax$ is $|F|^{-m}$-almost $\Delta$-universal. Over $\mathbb{F}_2$ this is the binary linear hash, which is $2^{-m}$-almost XOR-universal, and the same holds for every prefix of the rows of one public matrix.

## Proof sketch

If $x \ne x'$, pick $i$ with $x_i \ne x'_i$; the difference equals $\pm w_i$ plus a sum of weights independent of $w_i$, hence uniform. For matrices, $A \mapsto Av$ is a surjective additive map when $v \ne 0$. The multi-row bound is a hybrid argument conditioning on the shared weights.

## Depends on

- [Almost Δ-universal (difference-universal) hash families](almost-delta-universal-hash-family.md)
- [Leftover hash lemma](../../../../cryptography/randomness-extraction/leftover-hash-lemma.md)

## Sources

- C. Gentry, A. Sahai and B. Waters, "Homomorphic Encryption from Learning with Errors: Conceptually-Simpler, Asymptotically-Faster, Attribute-Based", CRYPTO 2013, 2013.
- I. Haitner and S. Vadhan, "The Many Entropies in One-Way Functions", in Tutorials on the Foundations of Cryptography, Springer, 2017.
- J. L. Carter and M. N. Wegman, "Universal Classes of Hash Functions", Journal of Computer and System Sciences, 1979.

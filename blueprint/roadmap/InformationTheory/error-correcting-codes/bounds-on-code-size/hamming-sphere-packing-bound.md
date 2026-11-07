# Hamming bound

Let $\alpha$ be a finite alphabet with $q \ge 2$ letters, and let $n$ and
$t$ be natural numbers. If $C$ is a set of words of length $n$ over $\alpha$ in which any two
distinct words are at Hamming distance at least $2t + 1$, then

$$|C| \sum_{i=0}^{t} \binom{n}{i} (q - 1)^i \le q^n.$$

The proof packs disjoint radius-$t$ Hamming balls around the codewords into the ambient space:
the distance hypothesis forces the balls apart (any overlap would give a triangle-inequality
contradiction), and each ball contains exactly $\sum_{i=0}^{t} \binom{n}{i} (q - 1)^i$ words.

This is the $q$-ary generalization of Hamming's binary sphere-packing bound. The original paper
assumes binary words and derives the $2^n$ form; the same disjoint-ball counting argument gives
the formula stated here for an arbitrary finite alphabet.

Binary source: R. W. Hamming, "Error Detecting and Error Correcting Codes",
Bell System Technical Journal 29 (1950), 147–160,
DOI 10.1002/j.1538-7305.1950.tb00463.x.

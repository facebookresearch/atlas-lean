# An exhaustive $q$-gram filter loses no pair within Hamming distance $k$

Let $w$, $q$ and $k$ be natural numbers with $q \le w$ and $kq < w - q + 1$, and let $R$ be a set of pairs of words of
length $w$ (the pairs a filter reports) that contains every pair sharing a positionally aligned [$q$-gram](q-gram.md).
Then $R$ contains every pair of words of length $w$ that differ in at most $k$ positions: such a pair
[shares an aligned $q$-gram](exists-q-gram-eq-of-mul-lt.md).

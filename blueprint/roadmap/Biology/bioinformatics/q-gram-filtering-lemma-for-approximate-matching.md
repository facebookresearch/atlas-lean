# q-gram (seed) filtering lemma for approximate matching

Let $w$, $q$ and $k$ be natural numbers with $q \le w$. If two strings $x$ and $y$ of length $w$ over an alphabet
differ in at most $k$ positions, then the number $s$ of offsets $i \in \{0, \dots, w - q\}$ at which their
[$q$-grams](q-gram.md) are equal (the positionally aligned $q$-grams they share: equal substrings of length $q$ at the
same offset) satisfies

$$w - q + 1 \le s + kq,$$

that is, they share at least $w - q + 1 - kq$ positionally aligned $q$-grams. The bound is written as a sum so that it
stays exact when $w - q + 1 - kq$ is negative. For $q = 0$ it holds trivially: all $w + 1$ offsets carry the empty
$q$-gram.

In particular, if $w - q + 1 > kq$, the two strings
[share at least one aligned $q$-gram](exists-q-gram-eq-of-mul-lt.md); consequently
[an exhaustive filter that reports every window pair sharing an aligned $q$-gram loses no pair at Hamming distance at most $k$](set-of-hamming-dist-le-subset.md).
This is a statement about exhaustive seeding; it is not a sensitivity guarantee for BLAST, whose extension and filtering
steps are heuristic.

## Proof

The aligned $q$-grams start at offsets $0, \dots, w - q$. A mismatch at position $j$ lies in the $q$-grams starting at
offsets $j - q + 1, \dots, j$ only, so it spoils at most $q$ of them, and at most $k$ mismatches spoil at most $kq$. The
remaining at least $w - q + 1 - kq$ aligned $q$-grams contain no mismatch and are equal.

## Related topics

- [Needleman–Wunsch score](sequence-alignment/pairwise-sequence-alignment/nw-score.md)

## Sources

- MIT 6.047 Computational Biology (Fall 2015), compiled lecture notes, Section 3.4 (the pigeonhole idea behind seed
  filtering in BLAST). The counting bound is derived above.
  <https://ocw.mit.edu/courses/6-047-computational-biology-fall-2015/pages/lectures_slides/>

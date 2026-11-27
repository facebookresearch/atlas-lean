# q-gram (seed) filtering lemma for approximate matching

Let $w$, $q$ and $k$ be integers with $1 \le q \le w$ and $k \ge 0$. If two strings of length $w$ differ in at most $k$
positions, they share at least $w - q + 1 - kq$ positionally aligned $q$-grams (equal substrings of length $q$ at the
same offset); in particular, if $w - q + 1 > kq$, they share at least one. Consequently an exhaustive filter that reports
every window pair sharing an aligned $q$-gram loses no pair at Hamming distance at most $k$ when $w - q + 1 > kq$.
This is a statement about exhaustive seeding; it is not a sensitivity guarantee for BLAST, whose extension and
filtering steps are heuristic, and the edit-distance version with its own bound is a separate page.

## Proof

The aligned $q$-grams start at positions $1, \dots, w - q + 1$. A mismatch at position $j$ lies in the $q$-grams starting at
positions $j - q + 1, \dots, j$ only, so it spoils at most $q$ of them, and at most $k$ mismatches spoil at most $kq$. The
remaining at least $w - q + 1 - kq$ aligned $q$-grams contain no mismatch and are equal.

## Related topics

- [Needleman–Wunsch score](sequence-alignment/pairwise-sequence-alignment/nw-score.md)

## Sources

- MIT 6.047 Computational Biology (Fall 2015), compiled lecture notes, Section 3.4 (the pigeonhole idea behind seed
  filtering in BLAST). The counting bound is derived above.
  <https://ocw.mit.edu/courses/6-047-computational-biology-fall-2015/pages/lectures_slides/>

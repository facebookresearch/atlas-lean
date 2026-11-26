# Random Tape TM

A binary Turing machine with $s$ control states, one read-only input tape, a write-only
output, $k$ ordinary work tapes and a read-only random tape. Tape number zero among the $k+1$
auxiliary tapes holds the random bits. Every table entry forbids writes to that tape but may
move its head. The table sees only the state and the symbols under the heads.

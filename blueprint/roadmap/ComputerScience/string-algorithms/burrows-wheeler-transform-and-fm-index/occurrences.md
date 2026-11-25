# Occurrences of a pattern reported by the FM-index

Let $t$ be a text and $P$ a pattern over a linearly ordered alphabet, let $SA$ be the suffix array
of $t$ followed by a sentinel smaller than every letter, and let $[sp, ep)$ be the interval returned
by backward search for $P$ on the Burrows–Wheeler transform of $t$. The occurrences of $P$ reported
by the FM-index are the suffix-array entries $SA[sp], SA[sp + 1], \dots, SA[ep - 1]$, in this
order (entries beyond the end of $SA$ are omitted).

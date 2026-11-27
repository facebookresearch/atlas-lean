# Linear probing succeeds exactly on partial parking functions

Let $s \le t$. A hash sequence $f : \{0, \dots, s - 1\} \to \{0, \dots, t - 1\}$ places all $s$
items in a table of $t$ cells by linear probing without wrap-around
([without overflow](lin-success.md)) if and only if $f$ is a
[partial parking function](is-partial-parking-function.md): for every cell $k$, at most $t - k$
items have hash address at least $k$.

For the forward direction, the items whose hash address is at least $k$ must all land in the
$t - k$ cells $k, \dots, t - 1$. The converse is the cluster argument. Hence
[Pollak's count of partial parking functions](pollak-partial-parking-functions-card.md) also
counts the hash sequences that linear probing without wrap-around places without overflow.

## Sources

- Don Knuth, "Notes on 'open' addressing", 22 July 1963, typeset by Helmut Prodinger in November 1997,
  Section 2 (non-overflow sequences) and Lemma 1: https://jeffe.cs.illinois.edu/teaching/datastructures/2011/notes/knuth-OALP.pdf

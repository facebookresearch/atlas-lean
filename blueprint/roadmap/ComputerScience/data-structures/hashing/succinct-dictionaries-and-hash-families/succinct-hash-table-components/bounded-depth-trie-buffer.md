# Bounded-depth character trie collision buffer

A *bounded-depth trie buffer* stores items keyed by reduced keys of $c \cdot b$ bits in a rooted $2^b$-ary trie of depth $c$, whose edges are labelled by the $c$ base-$2^b$ digits of the key. Each allocated node records its parent and incoming digit, and items are kept in an append-only log, so that lookup, insertion and deletion take $O(c)$ steps and the whole buffer can be cleared incrementally, one node per step, without scanning the $2^b$ children of any node. It holds the few keys whose fingerprints collide within a bucket during an epoch.

## Depends on

- [Universe-reduced two-stage hashing](../word-ram-hash-families/universe-reduced-two-stage-hashing.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul and W. Kuszmaul, "Modern Hashing Made Simple", Proceedings of the 2024 SIAM Symposium on Simplicity in Algorithms (SOSA), 2024.
- D. E. Knuth, "The Art of Computer Programming, Volume 3: Sorting and Searching", 2nd edition, Addison-Wesley, 1998.

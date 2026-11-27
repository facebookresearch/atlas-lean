# Bounded-depth character trie collision buffer

A *bounded-depth trie buffer* stores items keyed by reduced keys of $c \cdot b$ bits in a rooted $2^b$-ary trie of depth $c$, whose edges are labelled by the $c$ base-$2^b$ digits of the key. Each allocated node records its parent and incoming digit, and items are kept in an append-only log, so that lookup, insertion and deletion take $O(c)$ steps and the whole buffer can be cleared incrementally, one node per step, without scanning the $2^b$ children of any node. It holds the few keys whose fingerprints collide within a bucket during an epoch.

Tries of this kind are the buffers of the partition hash table of Bender, Farach-Colton, J. Kuszmaul and W. Kuszmaul: by their Lemma 2.2 a $k$-trie on $w$-bit keys takes $O(w/\log k)$ time per operation when its node arrays are pre-allocated and zeroed, and in their Section 5 two $\sqrt{n}$-tries of constant depth hold the pending insertions and deletions, not colliding fingerprints (a fingerprint collision there makes the bucket pick a fresh fingerprint function). The use as a fingerprint-collision buffer and the incremental clearing through parent records belong to a variant construction that is not in the cited sources.

## Depends on

- [Universe-reduced two-stage hashing](../word-ram-hash-families/universe-reduced-two-stage-hashing.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul and W. Kuszmaul, "Modern Hashing Made Simple", Proceedings of the 2024 SIAM Symposium on Simplicity in Algorithms (SOSA), pp. 363-373, 2024 (Lemma 2.2 and Section 5).
- D. E. Knuth, "The Art of Computer Programming, Volume 3: Sorting and Searching", 2nd edition, Addison-Wesley, 1998 (Section 6.3, digital searching).

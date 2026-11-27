# The inclusion property of LRU

Run LRU page replacement with capacities $k \le \ell$ on the same reference string, both starting
empty. After every prefix, the cache with $k$ frames is a prefix of the cache with $\ell$ frames
when both list their resident pages from most recent to least recent. Thus a hit in the smaller
cache is also a hit in the larger one, and increasing capacity cannot increase the number of
faults. This is the *stack property*, which rules out Belady's anomaly for LRU. At capacity zero
the cache always stays empty.

**Proof.** The distinct pages, ordered by their most recent references, are obtained by keeping
each page's last occurrence in the prefix and reversing the resulting list. LRU with $m$ frames
holds the first $m$ entries, or the whole list if fewer than $m$ pages have appeared. This holds
initially. On a request, move the requested page to the front, removing its old occurrence if
present. For positive $m$, every other page in the new first $m$ entries was already in the old
first $m$: if the requested page was inside that prefix, the other entries shift at most one
position; if it was outside, only the old first $m-1$ entries survive in the new prefix. For
$m=0$ no entries are kept. This proves the cache characterization by induction. Taking prefixes
of the same list now gives inclusion. Comparing the two hit indicators before each request and
summing the corresponding miss indicators gives the fault-count inequality.

FIFO does not have this property. With 3 and 4 frames on the reference string $1, 2, 3, 4, 1, 2, 5, 1, 2, 3, 4, 5$, FIFO incurs 9 and 10 faults respectively.

## Background

- [Belady's anomaly for FIFO page replacement](../../online-algorithms/competitive-paging/belady-s-anomaly-for-fifo-page-replacement.md)

## Sources

- R. H. Arpaci-Dusseau and A. C. Arpaci-Dusseau, *Operating Systems: Three Easy Pieces*, version 1.10, Chapter 22, "Beyond Physical Memory: Policies", <https://pages.cs.wisc.edu/~remzi/OSTEP/vm-beyondphys-policy.pdf>: the aside on Belady's anomaly, with FIFO on the reference string $1, 2, 3, 4, 1, 2, 5, 1, 2, 3, 4, 5$, and the stack property of LRU. The proof above is written out here.
- R. L. Mattson, J. Gecsei, D. R. Slutz and I. L. Traiger, "Evaluation techniques for storage hierarchies", *IBM Systems Journal* 9(2):78–117, 1970.

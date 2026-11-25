# The inclusion property of LRU

Run LRU page replacement with $k$ frames and with $k + 1$ frames on the same reference string, both starting empty. At every time, the set of pages held with $k$ frames is contained in the set held with $k + 1$ frames. Consequently the number of LRU page faults on a reference string is nonincreasing in the number of frames. LRU is a *stack algorithm*, and so does not exhibit Belady's anomaly.

**Proof.** By induction on time, LRU with $m$ frames holds exactly the $\min(m, d)$ most recently referenced distinct pages, where $d$ is the number of distinct pages referenced so far:
- a hit only reorders recency;
- a miss with a free frame adds the referenced page;
- a miss with all frames full evicts the least recently referenced held page, which is the $(m+1)$-st most recent distinct page once the new reference is counted.

The $k$ most recent distinct pages are among the $k + 1$ most recent, which gives inclusion. A reference that hits with $k$ frames is therefore also a hit with $k + 1$ frames.

FIFO does not have this property. With 3 and 4 frames on the reference string $1, 2, 3, 4, 1, 2, 5, 1, 2, 3, 4, 5$, FIFO incurs 9 and 10 faults respectively.

## Background

- [Belady's anomaly for FIFO page replacement](../../online-algorithms/competitive-paging/belady-s-anomaly-for-fifo-page-replacement.md)

## Sources

- R. H. Arpaci-Dusseau and A. C. Arpaci-Dusseau, *Operating Systems: Three Easy Pieces*, version 1.10, Chapter 22, "Beyond Physical Memory: Policies", <https://pages.cs.wisc.edu/~remzi/OSTEP/vm-beyondphys-policy.pdf>: the aside on Belady's anomaly, with FIFO on the reference string $1, 2, 3, 4, 1, 2, 5, 1, 2, 3, 4, 5$, and the stack property of LRU. The proof above is written out here.
- R. L. Mattson, J. Gecsei, D. R. Slutz and I. L. Traiger, "Evaluation techniques for storage hierarchies", *IBM Systems Journal* 9(2):78–117, 1970.

# Bit-packed slot tables for kick-tree dictionaries

The Word-RAM layout of a $k$-kick tree dictionary stores five parallel bit-packed arrays over the slots: quotients, values, a one-bit occupancy array, a one-bit elevated (kicked) array, and sparse slot metadata of a few bits. A slot query reads the occupancy bit before comparing the stored quotient with the target, so a stored value $0$ is distinguished from absence; zeroed memory is an empty table, and every slot read or write takes $O(1)$ instructions.

## Depends on

- [k-kick tree balls-to-slots scheme](k-kick-tree.md)
- [Bit-packed array on the Word RAM](../word-ram-hash-families/bit-packed-array.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul and M. Liu, "On the Optimal Time/Space Tradeoff for Hash Tables", Proceedings of the 54th ACM Symposium on Theory of Computing (STOC), 2022; arXiv:2111.00602.

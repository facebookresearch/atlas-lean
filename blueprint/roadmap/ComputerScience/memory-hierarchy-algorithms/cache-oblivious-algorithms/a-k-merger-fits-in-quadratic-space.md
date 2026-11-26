# A k-merger fits in quadratic space

A [$k$-merger](k-mergers.md) can be laid out in $O(k^2)$ contiguous memory locations. Its space satisfies $S(k) \le (\sqrt k + 1)S(\sqrt k) + O(k^2)$, the last term for the $\sqrt k$ buffers of size $2k^{3/2}$, whose solution is $S(k) = O(k^2)$.

## Depends on

- [k-mergers](k-mergers.md)

## Sources

- M. Frigo, C. E. Leiserson, H. Prokop and S. Ramachandran, "Cache-oblivious algorithms", *Proceedings of the 40th Annual Symposium on Foundations of Computer Science*, 1999, Section 4, Lemma 4 with its proof.

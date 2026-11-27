# k-mergers

In the [ideal-cache model](the-ideal-cache-model.md), a *$k$-merger* is a device that takes $k$ sorted input sequences and, each time it is invoked, outputs the next $k^3$ elements of their merge. The construction below is for arities $k = 2^{2^h}$, $h \ge 0$, so that every $\sqrt k$ in the recursion is again of this form; other arities, such as the $n^{1/3}$ of funnelsort, need a rounding or padding convention, which the source leaves implicit, and only the asymptotic space and cache bounds carry over. For $k = 2$ it is a direct merge. For larger $k$ it is built from $\sqrt k$ *left* $\sqrt k$-mergers $L_1, \dots, L_{\sqrt k}$, each fed by $\sqrt k$ of the inputs, $\sqrt k$ buffers of size $2k^{3/2}$ holding their outputs, and one *right* $\sqrt k$-merger $R$ that merges the buffers into the output. To output $k^3$ elements it invokes $R$ $k^{3/2}$ times; before each invocation it refills every buffer holding fewer than $k^{3/2}$ elements by invoking the corresponding left merger once. The buffers are maintained as circular queues, and the structure is laid out recursively in contiguous memory.

## Depends on

- [The ideal-cache model](the-ideal-cache-model.md)

## Sources

- M. Frigo, C. E. Leiserson, H. Prokop and S. Ramachandran, "Cache-oblivious algorithms", *Proceedings of the 40th Annual Symposium on Foundations of Computer Science*, 1999, Section 4 (the invariant of a $k$-merger, its recursive construction and Figure 3).

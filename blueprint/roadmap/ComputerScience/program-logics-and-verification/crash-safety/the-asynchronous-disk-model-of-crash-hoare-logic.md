# The asynchronous disk model of Crash Hoare logic

In the asynchronous disk model of Crash Hoare logic, a disk is a partial function from block numbers below its size to pairs $\langle v, vs \rangle$ of a last-written value $v$ and a finite set $vs$ of previous values. Reading a block returns its last-written value. Writing $v'$ to a block holding $\langle v, vs \rangle$ makes it hold $\langle v', \{v\} \cup vs \rangle$. A sync waits until every block's last-written value is on disk and discards the previous values, so each block then holds $\langle v, \emptyset \rangle$. Reading or writing a block number outside the disk fails. After a crash, each block independently holds one value chosen from $\{v\} \cup vs$, and then the recovery procedure runs on the resulting disk, with all previous values discarded. Writes are atomic at block granularity: no block ever holds part of a write.

## Sources

- H. Chen, D. Ziegler, T. Chajed, A. Chlipala, M. F. Kaashoek and N. Zeldovich, "Using Crash Hoare logic for certifying the FSCQ file system", *SOSP 2015*, Section 3 and Figure 3 (the asynchronous disk model)

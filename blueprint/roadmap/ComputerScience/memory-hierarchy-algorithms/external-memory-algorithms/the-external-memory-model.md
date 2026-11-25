# The external-memory model

The external-memory (I/O) model of Aggarwal and Vitter, in its single-disk form, has parameters $N$ (the number of records), $M$ (the number of records that fit in internal memory) and $B$ (the number of records transferred in one block), with $1 \le B \le M < N$. Internal memory and disk together form an array of at least $M + N$ record locations, $M$ of them internal. An I/O transfers at most $B$ records between internal memory and a contiguous segment of $B$ locations on the disk; records are indivisible. The cost of an algorithm is the number of I/Os it performs, internal computation being free. In this model the average-case and worst-case number of I/Os required to sort $N$ records is

$$\Theta\Bigl(\frac{N}{B} \cdot \frac{\log(1 + N/B)}{\log(1 + M/B)}\Bigr),$$

where, for the lower bound, the comparison model is used only when $B \log(1 + M/B) = o(\log(1 + N/B))$.

## Sources

- A. Aggarwal and J. S. Vitter, "The input/output complexity of sorting and related problems", *Communications of the ACM* 31(9):1116–1127, 1988, Sections 1 and 2 and Theorem 3.1 with $P = 1$

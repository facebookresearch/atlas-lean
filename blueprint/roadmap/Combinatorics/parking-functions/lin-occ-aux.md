# Occupied cells after linear probing without wrap-around

Let $f : \{0, \dots, s - 1\} \to \{0, \dots, t - 1\}$ be a hash sequence. For each $n$, this is
the set of cells occupied after the items $0, \dots, n - 1$ have been inserted in order, each
into the [first free cell at or after its hash address](lin-first-free.md), packaged with the
bound that it has at most $n$ elements. It is "none" as soon as some item finds no free cell
(overflow). There are no items with index $\ge s$, so the set stops changing after step $s$.

# Uniform probing at load at most one half needs at most two expected probes

In an open-addressed table of $m$ slots under uniform hashing (each key's probe sequence an independent uniform permutation of the slots), let $n$ keys be stored with $2 n \le m$. Then the expected number of slots inspected by an unsuccessful search, and by the insertion of a fresh key, is at most $m / (m - n) \le 2$, for every set of occupied slots of size $n$ and for every insertion history fixed in advance.

## Proof sketch

The probe sequence is a uniform permutation; the number of probes is one more than the number of leading occupied slots, whose expectation is $\sum_{i \ge 1} \prod_{j < i} \frac{n - j}{m - j} \le \sum_i (n/m)^i$, which equals the stated bound. The case $2n \le m$ gives $m/(m-n) \le 2$.

## Depends on

- [Expected probes in open addressing](../hashing-analysis/expected-probes-in-open-addressing.md)
- [Open-addressing hash table](../open-addressing/open-addressing.md)

## Proof depends on

- [Expected probes in open addressing](../hashing-analysis/expected-probes-in-open-addressing.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.

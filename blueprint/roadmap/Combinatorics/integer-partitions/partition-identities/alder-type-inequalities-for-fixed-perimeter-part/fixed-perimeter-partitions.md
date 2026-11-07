# Partitions with fixed perimeter

The perimeter of a partition is its largest part plus its
number of parts minus $1$. For a natural number $n$, the partitions with perimeter $n$ form the
finite set of all finite multisets $s$ of positive integers whose largest element plus number of
elements (counted with multiplicity) equals $n + 1$.

The set is enumerated directly: for each number of parts $k = 1, \dots, n$ the largest part is
$n + 1 - k$, and it is prepended to a multiset of $k - 1$ parts from $1, \dots, n + 1 - k$, so the
$2^{n-1}$ partitions with perimeter $n$ (for $n \ge 1$) are listed without filtering or
deduplication.

## Sources

- Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102, Section 1 (perimeter `Γ(π) = α(π) + λ(π) - 1`).

# Partitions with fixed perimeter

The perimeter of a partition is its largest part plus its
number of parts minus $1$. For a natural number $n$, the partitions with perimeter $n$ form the
finite set of all finite multisets $s$ of positive integers whose largest element plus number of
elements (counted with multiplicity) equals $n + 1$.

Equivalently, such a partition is determined by its number of parts $k \in \{1, \dots, n\}$,
its largest part $n + 1 - k$ and the multiset of its remaining $k - 1$ parts, taken from
$\{1, \dots, n + 1 - k\}$. Hence there are $2^{n-1}$ partitions with perimeter $n$ for $n \ge 1$,
and none for $n = 0$.

## Sources

- Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102, Section 1 (perimeter `Γ(π) = α(π) + λ(π) - 1`).

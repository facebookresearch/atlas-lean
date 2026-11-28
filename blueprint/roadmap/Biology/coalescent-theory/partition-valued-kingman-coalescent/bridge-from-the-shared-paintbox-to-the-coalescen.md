# From the paintbox to the partitions of the coalescent

This page covers a bridge between two encodings of random partitions.

[Kingman's paintbox representation](../../../Probability/foundations/exchangeable-random-partitions/kingman-paintbox-representation-of-exchangeable.md) builds an exchangeable random partition of $\mathbb{N}$ from a ranked mass sequence $s = (s_1 \ge s_2 \ge \cdots \ge 0)$ with $\sum_i s_i \le 1$ and a countable product of uniform variables on $[0, 1]$, and encodes it as an equivalence relation. The coalescent pages, such as [the rate matrix of Kingman's partition-valued coalescent](partition-rate.md), encode partitions as finite or coherent families of set partitions.

The bridge is an equivalence between the two encodings that preserves restriction to finite sets, exchangeability, and the frequencies of blocks. It reuses the paintbox definition of that page and does not create a second one.

## Expansion

State each part as a page of its own, with hypotheses fixed from a source:

1. The equivalence of encodings and its compatibility with restriction and permutation.
2. Checks: $s = 0$ gives the partition into singletons, $s = (1)$ gives one block, and two integers fall in the same block with probability $\sum_i s_i^2$.

Prerequisites:

- Measure, probability, integration and product measures.
- Finite partitions and their combinatorics.
- [Kingman paintbox representation of exchangeable random partitions](../../../Probability/foundations/exchangeable-random-partitions/kingman-paintbox-representation-of-exchangeable.md)

## Sources

- J. F. C. Kingman, The representation of partition structures, *J. London Math. Soc.* (2) 18 (1978), 374–380 (paintbox).
- N. Berestycki, Recent progress in coalescent theory, *Ensaios Matemáticos* 16 (2009), <https://arxiv.org/abs/0909.3985> (exchangeable partitions).

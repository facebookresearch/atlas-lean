# Rectangular permanents and the Binet–Minc identity

For an $m\times n$ matrix $b$ over a commutative ring, the *rectangular permanent* is $\mathrm{per}(b)=\sum_{\sigma}\prod_{r}b_{r,\sigma(r)}$, the sum over injections $\sigma$ from rows to columns. The Binet–Minc identity expresses it through power sums of row sums over the blocks of set partitions: for $m\le n$,

$$
\mathrm{per}(b)=\sum_{\pi}\prod_{B\in\pi}(-1)^{|B|-1}(|B|-1)!\sum_{c}\prod_{r\in B}b_{r,c},
$$

the sum over all set partitions $\pi$ of the rows.

## Proof sketch

Expand $\prod_{B\in\pi}\sum_c\prod_{r\in B}b_{rc}$ as a sum over maps from rows to columns that are constant on blocks; Möbius inversion on the partition lattice (whose Möbius function from the finest partition is $\prod_B(-1)^{|B|-1}(|B|-1)!$) isolates the injective maps.

## Depends on

- [Permanent of an encoded 0-1 matrix](../../../TheoryOfComputation/counting-complexity/complexity-of-the-permanent/perm-fun.md)

## Sources

- Michael A. Forbes, "Low-Depth Algebraic Circuit Lower Bounds over Any Field", 39th Computational Complexity Conference (CCC 2024), 2024.

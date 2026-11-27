# Fixed-weight support sampling in HQC

To sample a uniformly random vector of Hamming weight $w$ in $\mathbb{F}_2^n$, HQC draws $w$ independent fixed-width words $a_0, \dots, a_{w-1}$ and maps word $i$ into the shrinking interval $\{i, \dots, n-1\}$ by the multiply-high formula $c_i = i + \lfloor a_i (n - i) / 2^{b} \rfloor$. It then scans the candidates in descending index order and replaces any candidate already present among the later (already corrected) entries by its own index $i$. The result is a set of exactly $w$ distinct positions, returned as an indicator vector. This is a finite-precision version of the Fisher–Yates shuffle.

## Depends on

- [HQC public-key encryption](hqc-public-key-encryption.md)

## Sources

- Philippe Gaborit et al., "Hamming Quasi-Cyclic (HQC)", Version 5.1, November 9, 2026.

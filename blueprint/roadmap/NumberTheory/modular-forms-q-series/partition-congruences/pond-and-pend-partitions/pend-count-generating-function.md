# Generating function for PEND partitions

Let $\mathrm{pend}(n)$ be the number of PEND
partitions of $n$, and let $f_k = \prod_{m \ge 1} (1 - q^{km})$. Then, as integer power series
in $q$, $f_1 f_4 f_6 \sum_{n \ge 0} \mathrm{pend}(n) q^n = f_2 f_{12}$. This is the identity
$\sum_{n \ge 0} \mathrm{pend}(n) q^n = f_2 f_{12} / (f_1 f_4 f_6)$ with the denominator cleared.

## Sources

- James A. Sellers, *Elementary Proofs of Congruences for POND and PEND Partitions*, Journal of Integer Sequences 27 (2024), Article 24.4.7, Theorem 18 (`jis-2024-24.4.7-thm-18`).

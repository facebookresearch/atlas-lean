# Adaptive step-up false discovery rate bound with the discrete correction

Let $p_1, \dots, p_m$ be measurable, mutually independent p-values on a probability space, $H_0$ the set of true nulls, and nondecreasing nonnegative critical values $c_0 \le c_1 \le \dots$; the step-up procedure rejects $\{j : p_j \le c_{k^*}\}$ with $k^*$ the step-up index. If each true-null p-value satisfies $P(p_i \le t) \le F_i(t)$ with $F_i(c_m) < 1$, and $B \ge 0$ dominates $\frac1k\sum_{i \in S}F_i(c_k)/(1 - F_i(c_m))$ for $1 \le k \le m$ and every set $S \subseteq H_0$ of at most $m - k + 1$ true nulls, then the false discovery rate of the step-up procedure is at most $B$.

## Sources

- S. Döhler, G. Durand and E. Roquain, "New FDR bounds for discrete and heterogeneous tests", *Electronic Journal of Statistics* 12 (2018), 1867–1900.

# Heterogeneous step-up false discovery rate bound

Let $p_1, \dots, p_m$ be measurable, mutually independent p-values on a probability space, $H_0$ the set of true nulls, and nondecreasing nonnegative critical values $c_0 \le c_1 \le \dots$; the step-up procedure rejects $\{j : p_j \le c_{k^*}\}$ with $k^*$ the step-up index. If each true-null p-value satisfies $P(p_i \le t) \le F_i(t)$ and $b_i \ge F_i(c_k)/k$ for $1 \le k \le m$, then the false discovery rate of the step-up procedure is at most $\sum_{i \in H_0}b_i$. With $F_i(t) = t$ and $c_k = \alpha k/m$ this is the Benjamini–Hochberg bound $\alpha|H_0|/m$.

## Sources

- S. Döhler, G. Durand and E. Roquain, "New FDR bounds for discrete and heterogeneous tests", *Electronic Journal of Statistics* 12 (2018), 1867–1900.

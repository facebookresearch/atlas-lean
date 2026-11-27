# HKA's estimating equations

For $L$ loci, sample sizes $n_A, n_B$, parameters $\theta_1, \dots, \theta_L, T, f$ and counts $S^A_i, S^B_i, D_i$, the HKA estimating equations are

- $\sum_i S^A_i = a_1(n_A) \sum_i \theta_i$;
- $\sum_i S^B_i = f\, a_1(n_B) \sum_i \theta_i$;
- $\sum_i D_i = \bigl(T + \frac{1+f}{2}\bigr) \sum_i \theta_i$;
- $S^A_i + S^B_i + D_i = \theta_i \bigl(T + \frac{1+f}{2} + a_1(n_A) + f\, a_1(n_B)\bigr)$ for every locus $i$,

where $a_1(n) = \sum_{j=1}^{n-1} 1/j$ (Hudson, Kreitman & Aguadé 1987).

## Sources

- R. R. Hudson, M. Kreitman and M. Aguadé, *A test of neutral molecular evolution based on nucleotide data*, Genetics 116 (1987), 153–159.

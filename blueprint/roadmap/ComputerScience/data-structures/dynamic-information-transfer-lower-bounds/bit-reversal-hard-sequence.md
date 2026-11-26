# Bit-reversal interleaved operation sequence

For $n = 2^k$, the *bit-reversal sequence* for dynamic partial sums alternates $\mathrm{update}(\rho(t), g_t)$ and $\mathrm{sum}(\rho(t))$ for $t = 0, 1, \dots, n-1$, where $\rho(t)$ is the integer whose $k$-bit binary expansion is the reversal of that of $t$, and $g_0, \dots, g_{n-1}$ are independent uniformly random group elements. For every node of the information-transfer tree, the indices updated during $L_v$ and those queried during $R_v$ interleave perfectly, so that the answers of the queries in $R_v$ jointly determine the values written in $L_v$.

## Depends on

- [Dynamic partial sums over a group](dynamic-partial-sums-problem.md)
- [Information transfer and the information-transfer tree](information-transfer-tree.md)

## Sources

- Mihai Pătraşcu, Erik D. Demaine, "Logarithmic Lower Bounds in the Cell-Probe Model", SIAM Journal on Computing 35(4) (2006), arXiv:cs/0502041.

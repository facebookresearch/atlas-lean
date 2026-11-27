# Bit-reversal interleaved operation sequence

For $n = 2^k$, the *bit-reversal sequence* for dynamic partial sums alternates $\mathrm{update}(1 + \rho(t), g_t)$ and $\mathrm{sum}(1 + \rho(t))$ for $t = 0, 1, \dots, n-1$, on the array $A[1..n]$, where $\rho(t)$ is the integer whose $k$-bit binary expansion is the reversal of that of $t$, and $g_0, \dots, g_{n-1}$ are independent uniformly random group elements. Every index is touched by exactly one update and one query. If $\pi$ is the bit-reversal permutation of order $n$, that of order $2n$ is $\pi'(i) = 2\pi(i)$ and $\pi'(i + n) = 2\pi(i) + 1$, so the indices updated during the left half of any aligned block of operations and those queried during its right half alternate; each level of the information-transfer tree thus contributes interleaving $\Theta(n)$, for total interleaving $\Theta(n \lg n)$ (Pătraşcu–Demaine, Section 5.6). Consequently, given all operations outside $L_v$, the answers of the queries in $R_v$ determine the values written in $L_v$. Pătraşcu and Demaine prove their bounds with uniformly random indices and note that, since only the values $g_t$ need be random, the bounds for sum queries hold equally on this fixed index sequence.

## Depends on

- [Dynamic partial sums over a group](dynamic-partial-sums-problem.md)
- [Information transfer and the information-transfer tree](information-transfer-tree.md)

## Sources

- Mihai Pătraşcu, Erik D. Demaine, "Logarithmic Lower Bounds in the Cell-Probe Model", SIAM Journal on Computing 35(4) (2006), arXiv:cs/0502041.

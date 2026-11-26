# Greedy sequence with power-of-two averages

The following holds. Let $(a_n)_{n \ge 1}$ be a sequence of natural numbers with $a_1 = 1$ such that for every $n \ge 2$, $a_n$ is the least positive integer $x$ that is distinct from $a_1, \dots, a_{n-1}$ and satisfies

$$a_1 + \cdots + a_{n-1} + x = n \cdot 2^{\ell} \quad \text{for some } \ell \in \mathbb{N},$$

that is, the average of $a_1, \dots, a_{n-1}, x$ is a power of $2$. Then for every $n \ge 1$,

$$a_n = \begin{cases} (n + 1)\, 2^{n/2 - 1}, & n \text{ even}, \\ 2^{(n-1)/2}, & n \text{ odd}. \end{cases}$$

This is the reading of the source's Theorem 9 used in its proof: the printed statement takes the average of $a_1, \dots, a_{n-1}$ and omits distinctness, which would give $a_2 = 1$ instead of $3$.

## Sources

- Sela Fried, "Proofs of Several Conjectures From the OEIS", Journal of Integer Sequences 28 (2025), Article 25.4.3, Theorem 9.

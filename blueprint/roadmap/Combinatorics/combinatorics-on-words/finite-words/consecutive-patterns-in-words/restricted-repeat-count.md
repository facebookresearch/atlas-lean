# Words in which consecutive repeated letters differ

For $k, n \in \mathbb{N}$, $f_k(n)$ is the number of words $w = w_0 w_1 \cdots w_{n-1}$ of length $n$ over a $k$-letter alphabet with the following property: whenever $0 \le i < j$ with $j + 1 < n$, $w_i = w_{i+1}$ and $w_j = w_{j+1} = w_i$, there is $m$ with $i < m < j$ such that $w_m = w_{m+1} \neq w_i$. In words, no repeated letter equals the previous repeated letter.

## Sources

- Sela Fried, "Proofs of Several Conjectures From the OEIS", Journal of Integer Sequences 28 (2025), Article 25.4.3, Section 3.2.

# Erdős Problem 884 is false (Larsen)

For every real constant $C > 0$ there is a positive
integer $n$ whose divisors $d_1 < d_2 < \dots < d_t$, listed in increasing order, satisfy
$\sum_{1 \le i < j \le t} \frac{1}{d_j - d_i} >
C \left(1 + \sum_{1 \le i < t} \frac{1}{d_{i+1} - d_i}\right)$.

## Sources

- Lean proof of the negative answer to Erdős Problem 884, https://github.com/Jayyhk/erdos-lean/blob/f8a51976fd2e66a52b4928c109fb9ae877a1a507/problems/884/Erdos884.lean.

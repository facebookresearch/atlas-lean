# Jump consistent hash

*Jump consistent hash* assigns a key $k$ to one of $n \ge 1$ buckets numbered $0, \dots, n - 1$. In its idealized form the key seeds a sequence $U_1(k), U_2(k), \dots$ of independent random variables uniform on $[0, 1)$, and

$$
ch(k, n) = \max\bigl(\{0\} \cup \{ j : 1 \le j < n,\ U_j(k) < 1/(j + 1) \}\bigr),
$$

the result of starting from bucket $0$ and, for $j = 1, \dots, n - 1$ in turn, jumping to bucket $j$ when $U_j(k) < 1/(j+1)$. The practical algorithm replaces the uniform variables by the outputs of a 64-bit linear congruential generator seeded with the key and computes only the jumps, in expected logarithmic time; the buckets must be numbered consecutively, which suits data storage, where buckets are only added at the end.

## Sources

- J. Lamping and E. Veach, "A fast, minimal memory, consistent hash algorithm", arXiv:1406.2294, 2014, <https://arxiv.org/abs/1406.2294>, section "Explanation of the algorithm" (the linear-time algorithm and the generator) and the paragraph before it on data storage.

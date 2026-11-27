# Dimension and distance of binary Reed–Muller codes

For integers $0 \le r \le m$, the binary Reed–Muller code $\mathrm{RM}_2(r, m)$ is the set of evaluation vectors on $\mathbb{F}_2^m$ of the multilinear
polynomials of degree at most $r$ over $\mathbb{F}_2$. It is a linear code of length $2^m$, dimension $\sum_{i=0}^{r} \binom{m}{i}$ and minimum distance $2^{m-r}$.

## Depends on

- [Linear code](linear-codes/linear-code.md)
- [Minimum distance](linear-codes/min-dist.md)

## Related topics

- [Local decoding of the Hadamard code](hadamard-code-local-decoding.md): the Hadamard code is the homogeneous part of $\mathrm{RM}_2(1, m)$.
- [Hamming bound](bounds-on-code-size/hamming-sphere-packing-bound.md)

## Sources

- V. Guruswami, A. Rudra and M. Sudan, *Essential Coding Theory*, draft of August 26, 2025, Definition 9.1.3 and Theorem 9.3.3 (dimension and distance of $\mathrm{RM}(2, m, r)$). <https://cse.buffalo.edu/faculty/atri/courses/coding-theory/book/web-coding-book.pdf>

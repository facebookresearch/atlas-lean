# Reed-Muller codes and Hadamard local decoding

1. For integers $0 \le r \le m$, the binary Reed–Muller code $\mathrm{RM}_2(r, m)$, the evaluations on $\mathbb{F}_2^m$ of
   multilinear polynomials of degree at most $r$, has dimension $\sum_{i=0}^{r} \binom{m}{i}$ and minimum distance $2^{m-r}$.
2. The Hadamard code maps $x \in \mathbb{F}_2^m$ to the evaluations of the linear function $y \mapsto \langle x, y \rangle$ (homogeneous
   degree-1 polynomials). If a word $w : \mathbb{F}_2^m \to \mathbb{F}_2$ is within relative distance $\delta < 1/4$ of the Hadamard
   encoding of $x$, then for each $i \in \{1, \dots, m\}$ the decoder that picks $y$ uniformly at random and outputs
   $w(y) + w(y + e_i)$ returns $x_i$ with probability at least $1 - 2\delta$.

The two codes are stated separately; the Hadamard code is the homogeneous part of $\mathrm{RM}_2(1, m)$.

## Depends on

- [Linear code](linear-codes/linear-code.md)
- [Minimum distance](linear-codes/min-dist.md)

## Related topics

- [Hamming bound](bounds-on-code-size/hamming-sphere-packing-bound.md)

## Sources

- V. Guruswami, A. Rudra and M. Sudan, *Essential Coding Theory*, draft of August 26, 2025, Definition 9.1.3,
  Theorem 9.3.3 (dimension and distance of $\mathrm{RM}(2, m, r)$) and Definition 2.6.2 (Hadamard code). <https://cse.buffalo.edu/faculty/atri/courses/coding-theory/book/web-coding-book.pdf>
- S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, web draft of January 2007, Section 17.6.1 (local
  decoder for the Walsh–Hadamard code, success probability $1 - 2\rho$ for $\rho < 1/4$).
  <https://theory.cs.princeton.edu/complexity/book.pdf>

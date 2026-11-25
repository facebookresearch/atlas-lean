# Local decoding of the Hadamard code

The Hadamard code maps $x \in \mathbb{F}_2^m$ to the evaluation vector on $\mathbb{F}_2^m$ of the linear function $y \mapsto \langle x, y \rangle$. If a word
$w : \mathbb{F}_2^m \to \mathbb{F}_2$ is within relative distance $\delta < 1/4$ of the Hadamard encoding of $x$, then for each $i \in \{1, \dots, m\}$ the decoder
that picks $y \in \mathbb{F}_2^m$ uniformly at random, queries $w$ at $y$ and at $y + e_i$, and outputs $w(y) + w(y + e_i)$ returns $x_i$ with probability at least
$1 - 2\delta$.

Proof. The points $y$ and $y + e_i$ are each uniform, so by the union bound $w$ agrees with the encoding at both with probability at least $1 - 2\delta$, and then
$w(y) + w(y + e_i) = \langle x, y \rangle + \langle x, y + e_i \rangle = x_i$.

## Depends on

- [Linear code](linear-codes/linear-code.md)

## Related topics

- [Dimension and distance of binary Reed–Muller codes](reed-muller-codes-dimension-and-distance.md)

## Sources

- V. Guruswami, A. Rudra and M. Sudan, *Essential Coding Theory*, draft of August 26, 2025, Definition 2.6.2 (Hadamard code). <https://cse.buffalo.edu/faculty/atri/courses/coding-theory/book/web-coding-book.pdf>
- S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, web draft of January 2007, Section 17.6.1 (local
  decoder for the Walsh–Hadamard code, success probability $1 - 2\rho$ for $\rho < 1/4$).
  <https://theory.cs.princeton.edu/complexity/book.pdf>

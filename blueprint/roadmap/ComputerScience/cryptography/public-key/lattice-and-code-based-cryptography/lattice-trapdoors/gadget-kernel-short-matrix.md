# The gadget lattice has a short basis-like matrix $S_w$

Let $q = 2^w$ and let $S_w \in \mathbb{Z}^{w \times w}$ be lower bidiagonal with $2$ on the diagonal and $-1$ on the subdiagonal. Then every column of $S_w$ lies in $\Lambda_q^\perp(g^{\mathsf T}) = \{ z \in \mathbb{Z}^w : \langle g, z \rangle \equiv 0 \pmod q \}$, $\det S_w = 2^w$, every entry has absolute value at most $2$, and every column has squared Euclidean norm at most $5$. The block matrix $S = I_\ell \otimes S_w$ satisfies $G S \equiv 0 \pmod q$ with the same bounds. Moreover $G$ is primitive: $\{G x \bmod q : x \in \mathbb{Z}^{\ell w}\} = \mathbb{Z}_q^\ell$.

## Proof sketch

Column $j < w-1$ of $S_w$ is $2e_j - e_{j+1}$, with $\langle g, \cdot\rangle = 2^{j+1} - 2^{j+1} = 0$; the last column is $2 e_{w-1}$, giving $2^w \equiv 0$. The determinant of a triangular matrix is the product of its diagonal, and primitivity follows from $G\,G^{-1}(u) = u$.

## Depends on

- [The binary gadget vector and gadget matrix](gadget-matrix.md)
- [The short integer solution problem (SIS)](../lattice-problems/short-integer-solution-problem.md)

## Sources

- Daniele Micciancio and Chris Peikert, "Trapdoors for Lattices: Simpler, Tighter, Faster, Smaller", Advances in Cryptology – EUROCRYPT 2012, 2012.

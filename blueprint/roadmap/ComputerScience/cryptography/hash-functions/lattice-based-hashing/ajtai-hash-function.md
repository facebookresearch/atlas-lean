# Ajtai's hash function

For a modulus $q$, dimensions $n < m$ and a key $A \in \mathbb{Z}_q^{n \times m}$, *Ajtai's hash function* maps a vector $x \in \{0, 1\}^m$ (more generally $x \in \{0, \dots, \beta\}^m$) to

$$
h_A(x) = A x \bmod q \in \mathbb{Z}_q^n .
$$

The hash family $\{h_A\}$ is keyed by a uniformly random $A$. When $m > n \lceil \log_2 q \rceil$ it compresses $m$ bits to $n \lceil \log_2 q \rceil$ bits. A *collision* is a pair $x \ne y$ in the domain with $h_A(x) = h_A(y)$.

## Depends on

- [The short integer solution problem (SIS)](../../public-key/lattice-and-code-based-cryptography/lattice-problems/short-integer-solution-problem.md)

## Sources

- Miklós Ajtai, "Generating Hard Instances of Lattice Problems", Proceedings of the Twenty-Eighth Annual ACM Symposium on Theory of Computing (STOC '96), 1996.
- Oded Goldreich, Shafi Goldwasser and Shai Halevi, "Collision-Free Hashing from Lattice Problems", Electronic Colloquium on Computational Complexity, 1996.

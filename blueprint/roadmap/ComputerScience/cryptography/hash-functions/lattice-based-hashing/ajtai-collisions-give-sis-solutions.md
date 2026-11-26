# Collisions of Ajtai's hash give short integer solutions

Let $A \in \mathbb{Z}_q^{n\times m}$ with $q \ne 0$. If $x \ne y$ lie in $\{0, \dots, \beta\}^m$ and $A x \equiv A y \pmod q$, then $z = x - y$ is a short integer solution for $A$ with bound $\beta$. If instead $x \ne y$ lie in $\{-\beta, \dots, \beta\}^m$, then $x - y$ is a short integer solution with bound $2\beta$. Hence for every collision finder $F$ the algorithm "run $F$ and output the difference of its pair" solves SIS with at least the success probability of $F$, for every modulus, dimension and bound; no primality of $q$ is needed.

## Proof sketch

$h_A$ is $\mathbb{Z}$-linear, so $A(x - y) \equiv 0$; the difference is nonzero because $x \ne y$, and coordinatewise $|x_i - y_i| \le \beta$ (respectively $2\beta$).

## Depends on

- [Ajtai's hash function](ajtai-hash-function.md)
- [The short integer solution problem (SIS)](../../public-key/lattice-and-code-based-cryptography/lattice-problems/short-integer-solution-problem.md)

## Sources

- Miklós Ajtai, "Generating Hard Instances of Lattice Problems", Proceedings of the Twenty-Eighth Annual ACM Symposium on Theory of Computing (STOC '96), 1996.
- Oded Goldreich, Shafi Goldwasser and Shai Halevi, "Collision-Free Hashing from Lattice Problems", Electronic Colloquium on Computational Complexity, 1996.

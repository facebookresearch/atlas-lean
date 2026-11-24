# Hadamard matrices

For a natural number $m$, an $m \times m$ integer matrix $H$ is a Hadamard matrix when every entry is $1$ or $-1$ and $H^{\mathsf T} H = mI$.

## Idea

A Hadamard matrix has mutually orthogonal rows and columns of $\pm 1$ entries; one-sided orthogonality already implies the other side. Among $\pm 1$ matrices these are exactly the ones attaining Hadamard's determinant bound $|\det H| \le m^{m/2}$. They exist only for $m = 1, 2$ or $m$ divisible by $4$, and the Hadamard conjecture asserts existence for every multiple of $4$. Classical constructions take a circulant core bordered by a row and a column of ones: Paley's construction for $n + 1$ with $n$ a prime congruent to $3$ modulo $4$, and the twin-prime construction for $n = p(p + 2)$. Hadamard matrices are used in error-correcting codes, experimental design and signal processing.

## Statements

- [Hadamard matrix](is-hadamard-matrix.md)
- [One-sided orthogonality characterizes Hadamard matrices](is-hadamard-matrix-iff-is-hadamard.md): one-sided orthogonality characterizes them
- [A circulant core is a circulant submatrix](has-circulant-core-iff-circulant.md): circulant cores
- [Hadamard matrices with circulant core: Paley and twin-prime cases](exists-hadamard-matrix-with-circulant-co.md): the Paley and twin-prime constructions
- [Circulant-core Hadamard matrices with orthogonal rows and columns](exists-is-hadamard-with-circulant-core.md): the same constructions, with orthogonal rows and columns

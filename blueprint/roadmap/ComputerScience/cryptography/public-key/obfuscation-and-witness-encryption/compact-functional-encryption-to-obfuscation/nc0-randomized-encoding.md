# Degree-3 decomposable randomized encodings of log-depth computations

For every function $f:\{0,1\}^{n}\to\{0,1\}^{m}$ computable by a circuit of logarithmic depth (more generally by a polynomial-size branching program), there is a perfectly private, perfectly correct randomized encoding $\hat{f}(x;r)$ such that each output bit of $\hat{f}$ is a polynomial of degree at most $3$ over $\mathbb{F}_2$ depending on at most $4$ bits of $(x,r)$, and of degree $1$ in $x$. That is: from $\hat{f}(x;r)$ one decodes $f(x)$, and there is an efficient simulator $S$ with $S(f(x))\equiv\hat{f}(x;r)$ for uniform $r$. Under the existence of a PRG in $\oplus\mathsf{L}/\mathsf{poly}$, every polynomial-time function has a computationally private encoding of the same locality.

## Proof sketch

Write $f$ via a branching program whose output is the determinant of a matrix with affine entries; randomize the matrix by multiplying with random unipotent matrices on both sides, which preserves the determinant and makes the randomized matrix depend only on the output (Kilian-style randomization). Each entry is degree $3$ in input and randomness; a further splitting of terms reduces locality to $4$.

## Depends on

- [Pseudorandom generators exist if and only if one-way functions exist](../../../symmetric-key/pseudorandom-generators/pseudorandom-generators-exist-if-and-only-if.md)

## Sources

- Benny Applebaum, Yuval Ishai, Eyal Kushilevitz, "Cryptography in NC^0", SIAM Journal on Computing (2006).

# Nonsingular M-matrices

A real square matrix is a Z-matrix when its off-diagonal entries are nonpositive. A nonsingular M-matrix is a Z-matrix all of whose complex eigenvalues have positive real part; equivalently, its negative is Hurwitz stable.

## Idea

A Z-matrix can be written $A = sI - K$ with $K$ entrywise nonnegative, and it is a nonsingular M-matrix exactly when $s$ exceeds the spectral radius of $K$. Then the Neumann series $A^{-1} = s^{-1} \sum_{k \ge 0} (K/s)^k$ converges and has nonnegative terms, so a nonsingular M-matrix is invertible with an entrywise nonnegative inverse. Berman and Plemmons list dozens of equivalent conditions. M-matrices arise in discretized elliptic equations, Markov chains, economics (Leontief models) and epidemiology, where the next-generation matrix decides whether a disease-free state is stable.

## Statements

- [Nonsingular M-matrix](is-nonsingular-mmatrix.md)
- [Z-matrix](is-zmatrix.md): Z-matrices
- [Hurwitz matrix](is-hurwitz.md): Hurwitz-stable matrices: every eigenvalue has negative real part
- [Nonsingular M-matrices are invertible](is-unit.md): nonsingular M-matrices are invertible
- [Inverse positivity of M-matrices](inv-nonneg.md): their inverse is entrywise nonnegative
- [Neumann series](inv-one-sub-nonneg.md): $(I - K)^{-1}$ is entrywise nonnegative when $K \ge 0$ has spectral radius below $1$, proved with the Neumann series
- [Invertibility of 1 − K when the spectral radius is below one](is-unit-one-sub-of-spectral-radius-lt-on.md): $I - K$ is invertible when the spectral radius of $K$ is below $1$
- [Positive scalar matrices are nonsingular M-matrices](is-nonsingular-mmatrix-smul-one.md): an example: $cI$ for $c > 0$
- [Negative scalar matrices are Hurwitz](is-hurwitz-smul-one.md): an example: $cI$ for $c < 0$, used for the previous one
- [Spectrum of a real scalar matrix](spectrum-smul-one.md): used to find the eigenvalues in these examples
- [Complexification of a real scalar matrix](map-smul-one-algebra-map.md): used to compute that spectrum

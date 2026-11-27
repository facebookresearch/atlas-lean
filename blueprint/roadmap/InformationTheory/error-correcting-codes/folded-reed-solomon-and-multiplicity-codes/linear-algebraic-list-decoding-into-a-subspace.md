# Guruswami-Wang: the list of folded RS and multiplicity codes lies in a low-dimensional subspace

For folded Reed-Solomon codes and univariate multiplicity codes of order $s$ and rate $R$, and every $1 \le m \le s$, there is a polynomial-time algorithm that, given a received word, outputs an affine subspace of $\mathbb{F}_q[x]_{<k}$ of dimension at most $m - 1$ containing every message whose codeword is within relative distance

$$
\frac{m}{m+1}\left(1 - \frac{sR}{s - m + 1}\right)
$$

of the received word.

## Proof sketch

Interpolate a polynomial that is linear in the $y$-variables, $Q = A_0(x) + A_1(x)y_1 + \cdots + A_m(x)y_m$, vanishing at all windows; this needs only linear algebra. Any close message satisfies the functional equation $A_0(x) + \sum_j A_j(x) f(\gamma^{j-1} x) = 0$ (respectively with derivatives), a linear recurrence on the coefficients of $f$ whose solution space has dimension at most $m - 1$ because the leading coefficient structure determines all but $m - 1$ coefficients.

## Depends on

- [Folded Reed-Solomon codes](folded-reed-solomon-codes.md)
- [Univariate multiplicity codes](univariate-multiplicity-codes.md)

## Proof depends on

- [List recovery and relaxed generalized Singleton bounds](list-recovery-of-folded-codes.md)

## Sources

- Venkatesan Guruswami, Carol Wang, "Linear-algebraic list decoding for variants of Reed-Solomon codes", IEEE Transactions on Information Theory 59(6) (2013).

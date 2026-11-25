# The spectrum of a real 2 × 2 matrix is its set of characteristic roots

For a real $2 \times 2$ matrix $M$ and a complex number $z$, $z$ lies in the spectrum of $M$ over
$\mathbb{C}$, that is, of the complex matrix with the same entries, if and only if
$z^2 - (\operatorname{tr} M) z + \det M = 0$: the complex eigenvalues of $M$ are exactly the
[characteristic roots](is-char-root.md) of $(\operatorname{tr} M, \det M)$. This is the spectrum
used in the definition of
[Hurwitz matrices](../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/nonsingular-m-matrices/is-hurwitz.md).

In eigenvector form: there is a nonzero $v \in \mathbb{C}^2$ with $M v = z v$ if and only if
$z^2 - (\operatorname{tr} M) z + \det M = 0$, that is, if and only if $z$ is a characteristic root
of $(\operatorname{tr} M, \det M)$. The two forms agree because the spectrum consists of the values
with a [complex eigenvector](mem-spectrum-iff-exists-mul-vec-eq-smul.md).

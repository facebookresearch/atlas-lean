# Coefficient matrix of the squared voltage magnitude at a bus

For a natural number $n$ and an index $k$, the voltage coefficient matrix $E_k$ is the $n \times n$
matrix with entry $1$ at position $(k, k)$ and $0$ elsewhere. It is
[Hermitian](voltage-coeff-is-hermitian.md). Its [pairing](pairing.md) with any complex $n \times n$
matrix $W$ is the [real part of the diagonal entry](pairing-voltage-coeff.md) $W_{kk}$, which on the
[voltage lift](voltage-lift.md) of $V$ is the
[squared voltage magnitude](pairing-voltage-coeff-voltage-lift.md) $|V_k|^2$.

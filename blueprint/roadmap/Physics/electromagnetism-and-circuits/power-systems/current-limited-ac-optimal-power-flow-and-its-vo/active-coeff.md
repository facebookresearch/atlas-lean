# Coefficient matrix of the active power at a bus

For a natural number $n$, a complex $n \times n$ matrix $Y$ and an index $k$, the active coefficient
matrix is

$$A^P_k = \tfrac12 \bigl(R_k^{\mathsf H} + R_k\bigr),$$

with entries

$$(A^P_k)_{ab} = \tfrac12 \bigl(\delta_{bk}\, \overline{Y_{ka}} + \delta_{ak}\, Y_{kb}\bigr),$$

where $R_k$ keeps row $k$ of $Y$ and sets the other rows to zero ([row selection](row-select.md)).
It is [Hermitian](active-coeff-is-hermitian.md) for every $Y$. For Hermitian $W$ its
[pairing](pairing.md) with $W$ is the
[real part of the lifted injection](re-lifted-injection-eq-pairing.md)
$\sum_j \overline{Y_{kj}}\, W_{kj}$; when $Y$ is the [bus admittance matrix](bus-admittance.md) of a
network and $W = V V^{\mathsf H}$, it is the
[active power that bus k supplies to the network](pairing-active-coeff-voltage-lift.md).

# Coefficient matrix of the reactive power at a bus

For a natural number $n$, a complex $n \times n$ matrix $Y$ and an index $k$, the reactive
coefficient matrix is

$$A^Q_k = \frac{1}{2i} \bigl(R_k^{\mathsf H} - R_k\bigr),$$

with entries

$$(A^Q_k)_{ab} = \frac{1}{2i} \bigl(\delta_{bk}\, \overline{Y_{ka}} - \delta_{ak}\, Y_{kb}\bigr),$$

where $R_k$ keeps row $k$ of $Y$ and sets the other rows to zero ([row selection](row-select.md)).
It is [Hermitian](reactive-coeff-is-hermitian.md) for every $Y$. For Hermitian $W$ its
[pairing](pairing.md) with $W$ is the
[imaginary part of the lifted injection](im-lifted-injection-eq-pairing.md)
$\sum_j \overline{Y_{kj}}\, W_{kj}$; when $Y$ is the [bus admittance matrix](bus-admittance.md) of a
network and $W = V V^{\mathsf H}$, it is the
[reactive power that bus k supplies to the network](pairing-reactive-coeff-voltage-lift.md).

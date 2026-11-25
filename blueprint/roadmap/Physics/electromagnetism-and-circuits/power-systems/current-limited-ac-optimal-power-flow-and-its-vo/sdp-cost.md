# Linear active-generation cost of a matrix in the relaxation

For an [instance](current-limited-opf.md) of the current-limited optimal power flow problem with $n$
buses, [bus admittance matrix](admittance.md) $Y$, cost coefficients $c_k$ and active demands
$P^d_k$, and a complex $n \times n$ matrix $W$, the relaxation cost is

$$\sum_{k} c_k \bigl(\langle A^P_k, W \rangle + P^d_k\bigr),$$

where $A^P_k$ is the [active coefficient matrix](active-coeff.md) of $Y$ at bus $k$ and
$\langle A, W \rangle = \operatorname{Re} \operatorname{tr}(A W)$ is the [pairing](pairing.md). It
is defined for every $W$, feasible or not, and on the voltage lift of $V$ it
[equals the AC cost](sdp-cost-voltage-lift.md) of $V$.

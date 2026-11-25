# Voltage lift of a complex voltage vector

For a natural number $n$ and a complex vector $V \in \mathbb{C}^n$ of node voltages, the voltage
lift is the complex $n \times n$ matrix

$$W = V V^{\mathsf H}, \qquad W_{ab} = V_a\, \overline{V_b}.$$

It is [Hermitian](voltage-lift-is-hermitian.md) and
[positive semidefinite](voltage-lift-pos-semidef.md), of
[rank at most one](voltage-lift-rank-le-one.md), and
[unchanged by a common unit-modulus factor](voltage-lift-unit-mul.md) on $V$. On the lift of $V$,
the [pairings](pairing.md) with the [active](pairing-active-coeff-voltage-lift.md) and
[reactive](pairing-reactive-coeff-voltage-lift.md) coefficient matrices of the bus admittance matrix
of a network give the active and reactive powers that its buses supply, and those with the
[voltage](pairing-voltage-coeff-voltage-lift.md) and
[branch-current](pairing-branch-current-coeff-voltage-lif.md) coefficient matrices give the squared
voltage and branch-current magnitudes of the [optimal power flow problem](current-limited-opf.md).

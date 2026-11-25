# Voltage lift of a complex voltage vector

For a natural number $n$ and a complex vector $V \in \mathbb{C}^n$ of node voltages, the voltage
lift is the complex $n \times n$ matrix

$$W = V V^{\mathsf H}, \qquad W_{ab} = V_a\, \overline{V_b}.$$

It is Hermitian and [positive semidefinite](voltage-lift-pos-semidef.md), of
[rank at most one](voltage-lift-rank-le-one.md), and
[unchanged by a common unit-modulus factor](voltage-lift-unit-mul.md) on $V$. The bus powers and the
squared voltage and current magnitudes of the [optimal power flow problem](current-limited-opf.md)
are real-linear functions of $W$ when $W$ is a lift.

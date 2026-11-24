# Gauge strain is unchanged by a change of units

Let $u_1$ and $u_2$ be two choices of units, each a positive magnitude for every one of the seven
ISQ base quantities, and let

$$
s = \prod_{q} \left(\frac{u_1(q)}{u_2(q)}\right)^{e_q} > 0
$$

be the factor that converts a coordinate of the [voltage dimension](voltage-dim.md) from $u_1$ to
$u_2$, where $q$ runs over the base quantities and $e_q$ is the exponent of the voltage dimension at
$q$. Then for every gain $g \ne 0$, offset $b$ and voltage $V$, converting all three by $s$ leaves
the [strain](gauge-strain.md) unchanged:

$$
\frac{sV - sb}{sg} = \frac{V - b}{g}.
$$

The converted gain $sg$ is nonzero because $s > 0$.

# Horner evaluation of a constant polynomial

For every commutative semiring $R$,
every $x \in R$ and every single coefficient $a_0 \in R$ ($n = 1$), Horner evaluation of
$a_0$ at $x$ returns $a_0$ and charges $2$ operations.

The two operations are the multiplication $x \cdot 0$ and the addition $a_0 + x \cdot 0$,
which are executed because the accumulator starts at zero.

# Recursive matrix multiply-accumulate

Let $\alpha$ be a type with an addition and a
multiplication, let $k$ be a natural number and $n = 2^k$, and let $A$, $B$, $C$ be $n \times n$
matrices over $\alpha$, stored as vectors of rows. The procedure adds the product of $A$ and $B$
to the accumulator $C$ by the eight-call recursion of CLRS. When $n = 1$, writing $a$, $b$, $c$
for the single entries of $A$, $B$, $C$, it replaces $c$ by $c + ab$. Otherwise it splits each
matrix $M$ into four $(n/2) \times (n/2)$ quadrants $M_{11}$ (top left), $M_{12}$ (top right),
$M_{21}$ (bottom left) and $M_{22}$ (bottom right), and updates, in this order,
$C_{11} \gets C_{11} + A_{11} B_{11}$, $C_{12} \gets C_{12} + A_{11} B_{12}$,
$C_{21} \gets C_{21} + A_{21} B_{11}$, $C_{22} \gets C_{22} + A_{21} B_{12}$, then
$C_{11} \gets C_{11} + A_{12} B_{21}$, $C_{12} \gets C_{12} + A_{12} B_{22}$,
$C_{21} \gets C_{21} + A_{22} B_{21}$, $C_{22} \gets C_{22} + A_{22} B_{22}$, each by a
recursive call on the accumulator left by the previous one. It returns the final accumulator
together with two counters: the number of scalar multiplications and the number of accumulator
additions.

Only these two operations are charged; calls, indexing and allocation are free.

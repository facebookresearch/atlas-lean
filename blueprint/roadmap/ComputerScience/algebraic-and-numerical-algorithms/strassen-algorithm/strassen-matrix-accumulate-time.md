# Operation counts of Strassen's matrix accumulator

Let $R$ be a type with a zero, an
addition, a subtraction and a multiplication. For every $k \ge 0$ and all $2^k \times 2^k$
matrices $A$, $B$, $C$ over $R$, Strassen's accumulator on $A$, $B$, $C$ performs exactly $7^k$
scalar multiplications and exactly $(25 \cdot 7^k - 22 \cdot 4^k)/3$ scalar additions and
subtractions.

This count does not charge allocation or bit operations.

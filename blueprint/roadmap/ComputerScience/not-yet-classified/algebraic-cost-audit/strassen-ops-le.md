# Bound on the scalar operations of Strassen's accumulator

Let $R$ be a type with a zero,
an addition, a subtraction and a multiplication. For every $k \ge 0$ and all $n \times n$
matrices $A$, $B$, $C$ over $R$ with $n = 2^k$, the total number of scalar multiplications,
additions and subtractions that Strassen's accumulator performs on $A$, $B$, $C$, summed over all
its recursive calls, is at most $\frac{28}{3}\, n^{\log_2 7}$.

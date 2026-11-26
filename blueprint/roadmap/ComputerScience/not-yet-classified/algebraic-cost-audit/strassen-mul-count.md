# Multiplication count of Strassen's accumulator

Let $R$ be a type with a zero, an
addition, a subtraction and a multiplication. For every $k \ge 0$ and all $n \times n$ matrices
$A$, $B$, $C$ over $R$ with $n = 2^k$, Strassen's accumulator on $A$, $B$, $C$ performs exactly
$n^{\log_2 7}$ scalar multiplications, summed over all its recursive calls.

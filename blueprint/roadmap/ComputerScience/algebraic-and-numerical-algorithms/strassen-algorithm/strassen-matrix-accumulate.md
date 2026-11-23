# Strassen's matrix accumulator

Let $R$ be a type with a zero, an addition, a subtraction
and a multiplication (no ring axioms are assumed). For $k \ge 0$ and $2^k \times 2^k$ matrices
$A$, $B$, $C$ over $R$, this procedure runs Strassen's seven-product recursion for adding $AB$ to
$C$. It returns a $2^k \times 2^k$ matrix together with a pair of counts: the number of scalar
multiplications and the number of scalar additions and subtractions it performs.
For $k = 0$, with $a$, $b$, $c$ the single entries of $A$, $B$, $C$, it performs one
multiplication and one addition and returns the $1 \times 1$ matrix with entry $c + ab$.
For $k + 1$, write $X_{11}, X_{12}, X_{21}, X_{22}$ for the top-left, top-right, bottom-left and
bottom-right $2^k \times 2^k$ blocks of a matrix $X$. The procedure forms, entrywise,
$S_1 = B_{12} - B_{22}$, $S_2 = A_{11} + A_{12}$, $S_3 = A_{21} + A_{22}$,
$S_4 = B_{21} - B_{11}$, $S_5 = A_{11} + A_{22}$, $S_6 = B_{11} + B_{22}$,
$S_7 = A_{12} - A_{22}$, $S_8 = B_{21} + B_{22}$, $S_9 = A_{11} - A_{21}$ and
$S_{10} = B_{11} + B_{12}$; obtains $P_1, \dots, P_7$ by seven recursive calls with the zero
matrix as accumulator on the pairs $(A_{11}, S_1)$, $(S_2, B_{22})$, $(S_3, B_{11})$,
$(A_{22}, S_4)$, $(S_5, S_6)$, $(S_7, S_8)$ and $(S_9, S_{10})$; and returns the matrix with
blocks $C_{11} + P_5 + P_4 - P_2 + P_6$, $C_{12} + P_1 + P_2$, $C_{21} + P_3 + P_4$ and
$C_{22} + P_5 + P_1 - P_3 - P_7$, each sum formed entrywise from left to right.
Each entrywise scalar addition or subtraction adds one to the second count and each base-case
multiplication adds one to the first; indexing, allocation, copying and zero-fill are uncharged.

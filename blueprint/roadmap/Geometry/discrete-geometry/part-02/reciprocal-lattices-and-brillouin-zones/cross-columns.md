# Matrix of cross products of columns

For a real $3 \times 3$ matrix $B$ with columns $a_0, a_1, a_2$, let $X(B)$ be the matrix whose
$j$-th column is $a_{j+1} \times a_{j+2}$, indices modulo $3$: its columns are $a_1 \times a_2$,
$a_2 \times a_0$, $a_0 \times a_1$. It is defined for every $B$, singular or not, and equals the
transpose of the adjugate of $B$ ([adjugate identity](cross-columns-eq-transpose-adjugate.md)).

# Roads in Impartial Tak

Write the cells of the $n \times n$ board as pairs (row, column)
in $\{0, \dots, n-1\}^2$. Impartial Tak has ended at a set $S$ of occupied cells when the tokens
contain an orthogonal path from an edge of the board to the opposite edge: there are a token
$a \in S$ and a cell $b$ joined by a sequence $a = p_0, p_1, \dots, p_k = b$ with $k \ge 0$, in
which each $p_{i+1}$ is a token in $S$ orthogonally adjacent to $p_i$, such that $a$ lies in the
first column and $b$ in the last column, or $a$ lies in the first row and $b$ in the last row.

## Sources

- Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025), Article G1, Section 1 (rules of Impartial Tak).

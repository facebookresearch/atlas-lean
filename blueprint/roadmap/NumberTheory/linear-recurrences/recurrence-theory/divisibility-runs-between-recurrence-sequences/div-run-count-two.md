# Exact formula for the length-two run count

For every natural number $B$, let
$S(B) = \sum_{m=1}^{B} \left(2\lfloor B/m \rfloor + 1\right)$ and let $A_B(2)$ be the number of
integer tuples $(x, y, a, b, c) \in [-B, B]^5$ with $(x, y) \ne (0, 0)$ and
$(a, b, c) \ne (0, 0, 0)$ that have a divisibility run of length at least $2$. Then
$S(B) = 2 \sum_{m=1}^{B} \lfloor B/m \rfloor + B$ and $A_B(2) = 4(2B+1) S(B)^2 - 4B^2$.

## Sources

- Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Proposition 5.

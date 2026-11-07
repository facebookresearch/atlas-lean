# Exact formula for the length-one run count

For every natural number $B$, let
$D(B) = \sum_{m=1}^{B} \lfloor B/m \rfloor$ and let $A_B(1)$ be the number of integer tuples
$(x, y, a, b, c) \in [-B, B]^5$ with $(x, y) \ne (0, 0)$ and $(a, b, c) \ne (0, 0, 0)$ that have
a divisibility run of length at least $1$. Then

$$A_B(1) = 4(2B+1)^3 D(B) + 2B(2B+1)\left((2B+1)^2 - 1\right).$$

## Sources

- Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Proposition 4 (`integers-2026-A122-prop-4`).

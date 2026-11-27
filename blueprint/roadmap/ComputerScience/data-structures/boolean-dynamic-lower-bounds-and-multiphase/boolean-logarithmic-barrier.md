# The logarithmic barrier for Boolean dynamic problems

Before 2018 the strongest cell-probe lower bound for any explicit dynamic Boolean problem was $\Omega(\lg n)$, the Pătraşcu–Demaine information-transfer bound for dynamic connectivity, while problems whose queries return $\Theta(\lg n)$-bit answers admitted Larsen's bound $t_q = \Omega((\lg n/\lg(t_u w))^2)$ for two-dimensional weighted range counting, that is $\Omega((\lg n/\lg\lg n)^2)$ for $w = \Theta(\lg n)$ and polylogarithmic $t_u$, via cell sampling. Measured per output bit, both stay at $O(\lg n)$. Proving an $\omega(\lg n)$ lower bound for range parity was posed as one of five important open problems in Pătraşcu's obituary (Thorup 2013). A lower bound *crosses the logarithmic barrier* if it is $\omega(\lg n)$ for a Boolean problem.

## Depends on

- [Dynamic two-dimensional range parity](range-parity-problem.md)
- [Amortized update and query cost of a dynamic cell-probe structure](../dynamic-information-transfer-lower-bounds/amortized-cell-probe-costs.md)

## Sources

- Kasper Green Larsen, Omri Weinstein, Huacheng Yu, "Crossing the Logarithmic Barrier for Dynamic Boolean Data Structure Lower Bounds", STOC (2018); SIAM Journal on Computing (2020), arXiv:1703.03575.

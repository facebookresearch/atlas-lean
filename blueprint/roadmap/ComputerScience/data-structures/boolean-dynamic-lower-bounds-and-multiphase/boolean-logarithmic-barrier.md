# The logarithmic barrier for Boolean dynamic problems

Before 2018 the strongest cell-probe lower bound for any explicit dynamic Boolean problem with $w = \Theta(\lg n)$ and polylogarithmic updates was $\max\{t_u, t_q\} = \Omega(\lg n)$, from information transfer applied to Boolean problems such as dynamic connectivity, while non-Boolean problems admitted $\Omega((\lg n/\lg\lg n)^2)$ via cell sampling. Proving an $\omega(\lg n)$ lower bound for range parity was posed as one of the main open problems of the area. A lower bound *crosses the logarithmic barrier* if it is $\omega(\lg n)$ for a Boolean problem.

## Depends on

- [Dynamic two-dimensional range parity](range-parity-problem.md)
- [Partial sums over permutation groups reduce to connectivity of disjoint paths](../dynamic-information-transfer-lower-bounds/grid-permutation-reduction.md)
- [Pătraşcu–Demaine tradeoff for dynamic partial sums](../dynamic-information-transfer-lower-bounds/partial-sums-tradeoff.md)
- [Larsen's lower bound for dynamic range counting](../cell-sampling-and-range-counting-lower-bounds/dynamic-range-counting-lower-bound.md)

## Sources

- Kasper Green Larsen, Omri Weinstein, Huacheng Yu, "Crossing the Logarithmic Barrier for Dynamic Boolean Data Structure Lower Bounds", STOC (2018); SIAM Journal on Computing (2020), arXiv:1703.03575.

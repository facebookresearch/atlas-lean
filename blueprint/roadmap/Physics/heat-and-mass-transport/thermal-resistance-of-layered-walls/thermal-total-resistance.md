# Total resistance of a wall of n layers and two films

For a natural number `n`, reals `A`, `h_in`, `h_out` and sequences `L`, `k`, the total resistance is

`R = 1/(h_in A) + ∑_{i < n} L i/(k i A) + 1/(h_out A)`,

the formula of the [series resistance](thermal-series-resistance.md). With `x/0 = 0`, the inside
film term is `0` when `h_in A = 0`, the outside one when `h_out A = 0`, and a layer term when
`k i A = 0`. In the physical reading `A`, `h_in`, `h_out` and the `k i` are positive and the `L i`
nonnegative. On that domain it is [positive](thermal-total-resistance-pos.md).

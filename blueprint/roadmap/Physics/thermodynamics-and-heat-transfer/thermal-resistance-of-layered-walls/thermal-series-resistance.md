# Total series resistance of n layers between two surface films

For a natural number `n`, reals `A`, `h_in`, `h_out` and sequences `L`, `k`, the series resistance
is

`R = 1/(h_in A) + ∑_{i < n} L i/(k i A) + 1/(h_out A)`:

the inside film, the `n` planar layers of thicknesses `L i` and conductivities `k i`, and the
outside film, at the common area `A`. With `x/0 = 0`, the inside film term is `0` when `h_in A = 0`,
the outside one when `h_out A = 0`, and a layer term when `k i A = 0`. In the physical reading `A`,
`h_in`, `h_out` and the `k i` are positive and the `L i` nonnegative.

The same formula is the total resistance of the wall: the inside film, the layers and the outside
film in series. On the physical domain, with `L i ≥ 0` allowed, it is
[positive](thermal-total-resistance-pos.md).

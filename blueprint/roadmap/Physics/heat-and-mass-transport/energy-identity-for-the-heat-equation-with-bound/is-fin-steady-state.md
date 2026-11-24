# Steady state of a straight fin

For real `k`, `A`, `h`, `P`, `Ta` and `L` and functions `T` and `q` of position, the pair `(T, q)`
is a steady state of the fin on `[0, L]` if at every `x` with `0 ≤ x ≤ L`, with derivatives taken
within `[0, L]`,

`T′(x) = -q(x)/(kA)` (Fourier's law) and `q′(x) = -hP (T(x) - Ta)` (lateral convection).

Here `q` is the conducted heat rate in the `+x` direction, `k` the conductivity, `A` the
cross-section, `P` the perimeter, `h` the film coefficient and `Ta` the fluid temperature. With
`x/0 = 0`, the first equation reads `T′ = 0` when `kA = 0`. In the physical reading `k`, `A`, `h`,
`P` and `L` are positive.

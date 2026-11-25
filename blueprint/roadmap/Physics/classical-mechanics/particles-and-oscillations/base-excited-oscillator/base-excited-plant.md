# Base-excited oscillator as a state-space plant

For real numbers `m`, `c` and `k`, the base-excited oscillator as a state-space plant is the record
of four linear maps given by matrix–vector multiplication by the
[state matrix](base-excited-a.md) `A = [[0, 1], [-(k / m), -(c / m)]]`, the
[input matrix](base-excited-b.md) `B = [[0, 0], [1 / m, -1]]`, the
[output matrix](base-excited-c.md) `C = [1, 0]` and the [feedthrough matrix](base-excited-d.md)
`D = 0`, with state `(u, u') ∈ ℝ²`, input `(p, a_g) ∈ ℝ²` and output `u ∈ ℝ`. The record carries
no trajectory semantics; the trajectories of `x' = A x + B w` are characterised by the
[trajectory correspondence](base-excited-trajectory-iff.md) for `m > 0`. With the convention
`u / 0 = 0`, the entries `k / m`, `c / m` and `1 / m` are `0` when `m = 0`.

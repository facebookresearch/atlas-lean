# Moebius

The affine Möbius formula `(a z + b) / (c z + d)` of `g = !![a, b; c, d]` at `z : K`, with the
entries of `g` mapped to `K`. At a pole (`c z + d = 0`) it takes Lean's value `x / 0 = 0`;
`pmoebius_mk` identifies it with the projective action away from the pole.

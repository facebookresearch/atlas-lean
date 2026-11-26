# Kinematic certificate of the collapse mechanism

For a span `L > 0` and every real plastic moment `Mp`, the three-hinge mechanism with central
deflection `v = 2 / L` is normalized, `f · v = (L / 2) * (2 / L) = 1`, with the
[work vector](uniform-load-work.md) `f = (L / 2)`, and its plastic dissipation over the hinge
rotations `B v = (-4 / L ^ 2, 8 / L ^ 2, -4 / L ^ 2)`, with the
[hinge-rotation matrix](hinge-rotation.md) `B = (-2 / L, 4 / L, -2 / L)ᵀ` (a 3 × 1 matrix: rows the
critical sections at the left end, mid-span and right end; column the central deflection), is
`∑_e Mp * |(B v)_e| = 16 * Mp / L ^ 2` (Neal, Fig. 2.5(e)). The identities hold for every real `Mp`;
the physical reading of the dissipation is `Mp > 0`.

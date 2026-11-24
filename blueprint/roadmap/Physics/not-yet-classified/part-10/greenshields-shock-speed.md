# Front Speed

Greenshields shock speed between two distinct states. With
the Greenshields flux `greenshieldsFlux vf kj`, the shock speed
`ShockOrdering.shockSpeed (greenshieldsFlux vf kj) kL kR` between
distinct densities `kL ≠ kR` (with `kj ≠ 0`) is
`vf * (1 - (kL + kR) / kj)`. For complementary densities
(`kL + kR = kj`) the front is stationary.

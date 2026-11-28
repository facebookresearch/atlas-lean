# Signed edge counts of a walk

For each label `e : E`, the signed count of the walk's
darts over the oriented quotient edge `orb e`, that is, the sum of their indices relative to
`orb e`: a dart over `orb e` counts `1`, a dart whose reverse lies over it counts `-1`, and the
darts of an edge that `G` inverts count `0`. The endpoints of the walk are arbitrary, so its
image in the quotient graph need not be closed: under the trivial action on a single edge, the
one-step walk has count `1` and joins two different vertex orbits. `pathCycle` is the closed
case.

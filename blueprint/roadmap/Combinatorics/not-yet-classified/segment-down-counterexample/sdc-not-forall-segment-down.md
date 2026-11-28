# Sdc not forall segment Down

The segment-down condition cannot hold for every seed: if the off-support interior of `Vc` is
nonempty, then `rlc_SegmentDown Vc seed` fails for some `seed`. Take the lexicographically least
off-support interior site `z` and any other seed. The left neighbour of `z` is on `Vc`, and the row
below `z` contains no off-support interior site, so `z` has no segment-down witness.

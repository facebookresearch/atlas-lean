# Group impact under equal item curves

Two groups are placed on one
common latent scale: both latent laws `piA`, `piB` are finite PMFs on the same
state type `Z`, and each group's responses follow the latent-mixture law
`pi.bind (fun z => localIndepPMF (q z) ..)` with its own item curves
`qA`, `qB` in `[0, 1]`. If item `i` has the same conditional curve in both
groups (`qA z i = qB z i` for every latent state `z`), then the difference of
the groups' marginal success probabilities on item `i` is the latent-law
difference weighted by that common curve,
`∑ z, (piA z - piB z) * qA z i`. Equal curves therefore still allow a nonzero
marginal difference, and differing curves can still give equal marginals.
The identity needs the latent states of both groups to be the same scale
points; it says nothing about groups whose latent scales are not anchored to
each other.

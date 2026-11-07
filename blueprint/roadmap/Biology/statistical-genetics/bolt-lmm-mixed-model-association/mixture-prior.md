# Two-Gaussian mixture prior on a SNP effect

The BOLT-LMM prior on a SNP effect: the mixture `p N(0, v₁) + (1 - p) N(0, v₂)` of two
centered Gaussians with variances `v₁, v₂` (`v₂ = 0` gives the spike-and-slab prior with a point
mass at `0`).

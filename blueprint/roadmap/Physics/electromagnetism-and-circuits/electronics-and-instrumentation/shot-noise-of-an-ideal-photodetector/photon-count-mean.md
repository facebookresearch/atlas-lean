# Photon Count Mean

Poisson mean `λ T` of the count in a window of length `T`, as a nonnegative real. It is that
mean for physical inputs (nonnegative efficiency and power, positive `h`, `ν` and window length;
`coe_photonCountMean`); a negative raw product `λ T` from unphysical inputs is clamped to `0` by
`toNNReal`.

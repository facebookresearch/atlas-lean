# Final register represents shifted message remainder of monic

The leaf obligation at v2 strength: for any monic `g` of degree `r` (including `r = 0`,
where `g = 1`), the register run with taps `g.toBitVec r` represents `(m * X ^ r) %ₘ g`.

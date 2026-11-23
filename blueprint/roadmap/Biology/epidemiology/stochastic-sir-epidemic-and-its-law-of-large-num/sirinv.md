# Bookkeeping invariant

**Bookkeeping invariant** of the constructed SIR chain after `n` jumps, with `k₁`
infections and `k₂` recoveries so far: the counts are `S = S₀ - k₁`, `I = I₀ + k₁ - k₂`; the
future interarrivals of each clock are its interarrivals after the ones consumed; the internal
clock plus the residual is the next arrival time; the internal clock is at least the last
arrival time; and the residuals are positive.

# Cpa Tape Reduction

The distinguisher (for the keyed function queried by `encQ`) built from a CPA adversary: with
its own coins `(b, r, ρ, rs)` it runs the adversary on coins `r`, simulating each encryption query
and the challenge `Enc(m_b)` with `encQ` and the randomness `ρ` and `rs`, and outputs whether the
adversary guessed `b`.

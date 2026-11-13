# Det Mac

A **deterministic MAC with canonical verification** (Katz and Lindell, Section 4.2 and
Construction 4.5): `Mac_k(m) = tagF k m`, and `Vrfy_k(m, t) = 1` iff `t = tagF k m`. For such
MACs existential unforgeability is already strong unforgeability (Katz and Lindell,
Section 4.2), which is why the framework's `macGame` suffices below.

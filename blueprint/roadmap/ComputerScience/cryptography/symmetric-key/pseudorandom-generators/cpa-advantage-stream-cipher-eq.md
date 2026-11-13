# The stream cipher is eavesdropping-secure if the PRG is pseudorandom

**The stream cipher is eavesdropping-secure if the PRG is pseudorandom** (Katz and Lindell,
Theorem 3.18), as an exact equality: for every eavesdropper `A` (a CPA adversary making no
queries), its advantage against the stream cipher is the PRG advantage of `cpaReduction A`.

# Coin Scheme

A private-key encryption scheme with **explicit encryption randomness**:
`Enc_k(m) = encR k m r` for `r ← ρ`. Every scheme whose encryption algorithm reads a random tape
has this form; reductions in the framework are deterministic after their coins, so they can
only simulate encryption when its randomness is explicit.

# Sigma Sim At

The **per-challenge Schnorr simulator**: for the challenge `r`, a uniform answer `s` and the
commitment `g ^ s * (y ^ r)⁻¹`, computed from the statement `y` alone. It is `Schnorr.simulate`
with the challenge fixed to `r`.

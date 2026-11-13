# The stream cipher

**The stream cipher** from a PRG (Katz and Lindell, Construction 3.17, over an additive group
of messages): the key is a uniform seed `k`, `Enc_k(m) = G k + m` and `Dec_k(c) = c - G k`.

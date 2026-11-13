# ElGamal

**ElGamal** (Katz and Lindell, Construction 11.16) as a framework `PKEScheme`: key generation
samples a uniform secret key `x` and publishes `g ^ x`; encryption samples uniform randomness
`y` and outputs `encrypt g h m y = (g ^ y, h ^ y * m)`.

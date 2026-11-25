# Monic Modulus to Bit Vec

The taps word of a monic binary polynomial recovers it as the canonical
modulus `X^s + taps`: `(f.toBitVec s).monicModulus = f` whenever `f.Monic` and
`f.natDegree = s`.

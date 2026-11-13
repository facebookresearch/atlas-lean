# Param Gen

Pedersen parameter generation: `h = g ^ x` for a uniform unit `x` of `ZMod q`. For `q` prime
the units are exactly the nonzero exponents, so `h ≠ 1` whenever `g` has order `q`
(`ne_one_of_mem_support_paramGen`), which is the generator condition of perfect hiding.

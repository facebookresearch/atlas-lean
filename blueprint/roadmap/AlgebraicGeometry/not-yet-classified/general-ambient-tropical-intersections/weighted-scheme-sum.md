# Weighted Scheme Sum

The sum of the local length coefficients `length(O_Z / (I + J))` times the tropical
multiplicities. Each length is converted with `ENat.toNat`, so this is the intended sum only when
every local length is finite, as it is when the local Tor modules have finite length
(`weightedSum_of_higherTor_zero`).

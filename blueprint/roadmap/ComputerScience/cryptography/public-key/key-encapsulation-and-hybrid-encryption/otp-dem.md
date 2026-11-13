# Otp DEM

The group one-time pad as a DEM (Katz and Lindell, Section 11.4.1): CSLib's `groupOTP G`
(uniform key `k`, `Enc_k(m) = k m`, `Dec_k(c) = k⁻¹ c`) embedded by
`SymmEncScheme.ofEncScheme`.

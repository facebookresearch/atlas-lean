# PRF-based encryption is correct

For every keyed function `F : K → X → Y`, the PRF-based encryption scheme
`prfEnc F` is correct: decrypting an encryption of `m` returns `m`.

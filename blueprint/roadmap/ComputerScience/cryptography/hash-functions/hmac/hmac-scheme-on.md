# HMAC as a MAC on encoded messages

HMAC as a MAC (Katz and Lindell, Definition 4.1) on messages of a type `X`
encoded into bit strings by `enc`: the PRF-MAC (Construction 4.5) of the keyed
function `k, x ↦ HMAC_k(enc x)`, with a uniform `n`-bit key, the tag
`HMAC_k(enc x)`, and verification by recomputing the tag. The case `enc = id`
is HMAC on all bit strings.

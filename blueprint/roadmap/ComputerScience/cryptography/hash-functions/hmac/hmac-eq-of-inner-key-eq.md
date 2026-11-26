# HMAC depends on the key only through the derived keys

Let `0 < n`. If two `n`-bit keys `k` and `k'` have the same inner derived key
`h(iv, k ⊕ ipad)` and the same outer derived key `h(iv, k ⊕ opad)`, then
`HMAC_k(m) = HMAC_{k'}(m)` for every message `m`.

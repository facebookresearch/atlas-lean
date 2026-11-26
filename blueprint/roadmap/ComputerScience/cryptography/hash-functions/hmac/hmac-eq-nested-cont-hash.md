# HMAC in nested form

Let `0 < n`. For an `n`-bit key `k` and a message `m`, with the derived
chaining values `h(iv, k ⊕ ipad)` and `h(iv, k ⊕ opad)`, `HMAC_k(m) =
H'_{h(iv, k ⊕ opad)}(H'_{h(iv, k ⊕ ipad)}(m))`, where `H'` is the continuation
hash (Katz and Lindell, Section 5.3.2).

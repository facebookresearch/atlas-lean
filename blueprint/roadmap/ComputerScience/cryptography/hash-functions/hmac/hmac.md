# HMAC

**HMAC** (Katz and Lindell, Construction 5.7):
`HMAC_k(m) = H((k ⊕ opad) ‖ H((k ⊕ ipad) ‖ m))` for the double-length-encoded Merkle–Damgård
hash `H = fullHash`.

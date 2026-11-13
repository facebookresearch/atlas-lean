# Encrypt-then-authenticate

**Encrypt-then-authenticate** (Katz and Lindell, Section 4.5): with independent keys
`k₁, k₂`, `Enc_{k₁,k₂}(m) = (c, Mac_{k₂}(c))` for `c ← Enc_{k₁}(m)`; decryption returns `⊥`
unless the tag verifies, and then decrypts `c`.

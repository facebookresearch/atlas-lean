# Lamport one-time signature scheme

Lamport's one-time signature scheme for `ℓ`-bit messages and a function `f : X
→ Y`, with `X` finite and nonempty and equality on `Y` decidable (Katz and Lindell, Section 12.6.1): the secret key `sk : Fin ℓ × Bool →
X` is uniform, the public key is `f ∘ sk`, and signing is deterministic,
revealing `sk (i, m i)` for each bit position `i`.

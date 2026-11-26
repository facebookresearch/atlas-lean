# Lamport one-time signature security bound

Let `f : X → Y` with `X` finite and nonempty and `Y` with decidable equality,
let the forger's coins `R` be finite and nonempty, and let `ℓ ≠ 0` be the
message length. For every forger `A`, the signature-forgery advantage of `A`
against the Lamport scheme `lamport f` is at most `2 * ℓ` times the
probability that the derived inverter `invert f A` wins the one-wayness game
for `f` (Katz and Lindell, Theorem 12.16).

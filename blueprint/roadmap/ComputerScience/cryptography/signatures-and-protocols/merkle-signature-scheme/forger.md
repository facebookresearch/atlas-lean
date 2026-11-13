# Forger

An adaptive forger against the stateful Merkle signer, with random coins in `R`: from the
public key (the root) and its coins it queries the signing oracle, whose answers are
`Option (Signature X Y A ℓ)` (`none` once the keys are used up), and outputs a message and a
signature.

# Forger against Merkle signatures

An adaptive forger against the stateful Merkle signer, with random coins in a set $R$, receives the
public key (the root) and its coins, queries a signing oracle whose answers are signatures (or
nothing, once the keys are used up), and outputs a message and a signature.

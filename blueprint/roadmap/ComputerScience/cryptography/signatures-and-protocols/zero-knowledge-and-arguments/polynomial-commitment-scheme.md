# Polynomial Commitment Scheme

Distributional interface for the six operations at degree bound `t`. Setup at security
parameter `κ` samples a public/secret key pair; the public key determines the prime and all the
remaining operations. The full commitment and verifier are an ordinary correct commitment
scheme. Full opening returns the polynomial and decommitment, and witness creation attaches the
requested index and the polynomial's value to a sampled witness. Every supported honest witness
verifies. Keys range over well-formed public keys; no subsequent operation takes the setup
secret. The PMFs and Boolean functions specify distributions and decisions, not a uniform
implementation or time bound.

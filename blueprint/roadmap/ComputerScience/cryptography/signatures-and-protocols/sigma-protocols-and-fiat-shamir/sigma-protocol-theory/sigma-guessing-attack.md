# Generic guessing impersonation against Sigma protocols

Let $\Pi$ be special HVZK with a simulator whose outputs are always accepting. The *guessing impersonator* guesses a challenge $c$ uniformly, simulates an accepting $(t, z)$ for $c$, sends $t$, and answers $z$ if the verifier's challenge equals $c$. In the direct-attack identification game it succeeds with probability at least $1/|C|$, without any knowledge of a witness. Hence the challenge set of an identification protocol must be superpolynomially large (or the protocol repeated) for security.

## Proof sketch

The guessed challenge matches the uniform verifier challenge with probability $1/|C|$, and then the simulated conversation is accepting.

## Depends on

- [A Sigma protocol](../../zero-knowledge-proofs/sigma-protocol.md)
- [Perfect special honest-verifier zero knowledge](../../zero-knowledge-proofs/special-hvzk.md)

## Sources

- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.

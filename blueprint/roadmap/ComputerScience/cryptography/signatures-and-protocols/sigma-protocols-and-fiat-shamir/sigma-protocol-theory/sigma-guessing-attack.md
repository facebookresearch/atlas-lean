# Generic guessing impersonation against Sigma protocols

Let $\Pi$ be special HVZK with a simulator whose outputs are always accepting. The *guessing impersonator* guesses a challenge $c$ uniformly, simulates an accepting $(t, z)$ for $c$, sends $t$, and answers $z$ if the verifier's challenge equals $c$. In the direct-attack identification game it succeeds with probability at least $1/|C|$, without any knowledge of a witness. Hence the challenge set of an identification protocol must be superpolynomially large (or the protocol repeated) for security.

## Proof sketch

The guessed challenge matches the uniform verifier challenge with probability $1/|C|$, and then the simulated conversation is accepting.

## Depends on

- [A Sigma protocol](../../zero-knowledge-proofs/sigma-protocol.md)
- [Perfect special honest-verifier zero knowledge](../../zero-knowledge-proofs/special-hvzk.md)

## Sources

- C. P. Schnorr, "Efficient Signature Generation by Smart Cards", Journal of Cryptology 4, 1991, pp. 161–174.
- Thomas Attema, Ronald Cramer and Lisa Kohl, "A Compressed Σ-Protocol Theory for Lattices", Advances in Cryptology – CRYPTO 2021, Springer, 2021, Section 3.3.

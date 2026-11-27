# A guessing impersonator against Schnorr identification

For Schnorr identification with challenges drawn uniformly from a set of size $2^{k(n) n}$, the impersonator that guesses the challenge $c$ in advance, sends the simulated commitment $t = g^{z} u^{-c}$ for uniform $z$, and replies $z$ succeeds with probability at least $2^{-k(n)n}$ and runs in polynomial time. Hence security requires the challenge space to be super-polynomial.

## Proof sketch

If the verifier's challenge equals the guess, the conversation $(t, c, z)$ is accepting by construction.

## Depends on

- [Schnorr verifier's acceptance condition](../../schnorr-identification-scheme/accepts.md)

## Sources

- C. P. Schnorr, "Efficient Signature Generation by Smart Cards", Journal of Cryptology 4 (1991), 161–174.

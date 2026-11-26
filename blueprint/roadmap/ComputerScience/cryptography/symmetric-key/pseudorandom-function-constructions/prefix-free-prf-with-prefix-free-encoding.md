# A prefix-free PRF composed with a prefix-free encoding is a variable-length PRF

If $F$ is a prefix-free PRF on $X^{\le \ell}$ and $\mathrm{pf} : M \to X^{\le \ell}$ is an efficiently computable prefix-free encoding, then $F'(k, m) = F(k, \mathrm{pf}(m))$ is a PRF on $M$ against arbitrary (not necessarily prefix-free) adversaries, with the same advantage.

## Proof sketch

Any adversary for $F'$ becomes a prefix-free adversary for $F$ by encoding its queries, since encodings of distinct messages are never prefixes of one another; repeated messages are answered consistently.

## Depends on

- [Prefix-free encoding of messages](prefix-free-encoding.md)
- [Asymptotic PRF security relative to a class of distinguishers](../pseudorandom-functions/prfsecure.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.

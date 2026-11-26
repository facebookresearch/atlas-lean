# CBC-MAC from a secure PRF is computationally universal

If $F$ is a PRF on $n$-bit blocks with $2^{-n}$ negligible, then raw CBC-MAC on nonempty messages of $1$ to $\ell(n)$ blocks is a computational universal hash function and multi-query secure. For an adversary outputting $Q$ messages the advantage is at most

$$\mathrm{PRFadv}(F) + \binom{Q}{2}\frac{\ell^2 + \ell}{2^n},$$

where the PRF distinguisher makes at most $Q\ell$ queries.

## Proof sketch

A PRF distinguisher runs the adversary, evaluates raw CBC-MAC with its oracle on the $Q$ output messages and outputs $1$ iff two distinct messages get equal values. With a truly random function in place of $F$, two distinct messages of $m$ and $m'$ blocks ($1 \le m, m' \le \ell$, one possibly a prefix of the other) collide with probability at most $mm'/2^n + \max(m, m')/2^n \le (\ell^2 + \ell)/2^n$ by the CBC collision bound; a union bound over the $\binom{Q}{2}$ pairs finishes.

## Depends on

- [CBC-MAC](../cbc-mac-and-mac-security/cbc-mac.md)
- [Computational universal hash function](computational-universal-hash.md)

## Proof depends on

- [PRF advantage](../pseudorandom-functions/prf-advantage.md)

## Sources

- J. Black and P. Rogaway, "CBC MACs for Arbitrary-Length Messages: The Three-Key Constructions", Journal of Cryptology 18(2), 2005 (CBC collision bound for a random function and distinct messages of possibly different lengths).
- M. Bellare, "New Proofs for NMAC and HMAC: Security without Collision-Resistance", Journal of Cryptology 28(4), 2015 (the cAU notion and the reduction from a PRF distinguisher that queries both messages and tests for equal replies).

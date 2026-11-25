# Security of the Boneh–Franklin identity-based encryption scheme

An identity-based encryption scheme consists of algorithms Setup, Extract (deriving the private key of an identity from the master secret), Encrypt (using the public parameters and an identity) and Decrypt. It is IND-ID-CPA secure if no efficient adversary that may obtain private keys of identities of its choice, other than a challenge identity it selects, can distinguish encryptions of two messages of its choice under the challenge identity with non-negligible advantage. In Boneh and Franklin's scheme BasicIdent over a bilinear group, with hash functions $H_1$ and $H_2$ modelled as random oracles, IND-ID-CPA security reduces to the bilinear Diffie–Hellman assumption with a loss polynomial in the number of hash and extraction queries.

## Depends on

- [Pairing-based assumptions: BDH and t-SDH](pairing-based-assumptions-bdh-and-t-sdh.md)
- [The random oracle model](../random-oracle-constructions/the-random-oracle-model.md)
- [Public-key encryption scheme](../../security-games/generic-security-games/pkescheme.md)

## Sources

- D. Boneh and M. Franklin, "Identity-based encryption from the Weil pairing", *SIAM Journal on Computing* 32(3):586–615, 2003, Theorem 4.1

# Correctness of the Fujisaki–Okamoto KEMs

If $\mathrm{PKE}$ is $\delta$-correct, then in the random oracle model the KEMs $\mathrm{FO}^{\perp}$ and $\mathrm{FO}^{\not\perp}$ are $q_G \delta$-correct against adversaries making at most $q_G$ queries to $G$: the probability that an honestly encapsulated key fails to be recovered by decapsulation is at most $q_G\delta$.

## Proof sketch

Decapsulation of an honest ciphertext succeeds unless the coins $G(m)$ cause a decryption error; the adversary can test at most $q_G$ messages, each failing with probability at most the worst-case message failure probability of its key, whose average over keys is $\delta$.

## Depends on

- [The KEM transforms $U^{\perp}$ and $U^{\not\perp}$ and the Fujisaki–Okamoto KEMs](transforms-u-and-fo-kems.md)
- [Correctness of a key-encapsulation mechanism](../../key-encapsulation-and-hybrid-encryption/correct.md)

## Sources

- Dennis Hofheinz, Kathrin Hövelmanns and Eike Kiltz, "A Modular Analysis of the Fujisaki–Okamoto Transformation", Theory of Cryptography (TCC 2017), 2017.

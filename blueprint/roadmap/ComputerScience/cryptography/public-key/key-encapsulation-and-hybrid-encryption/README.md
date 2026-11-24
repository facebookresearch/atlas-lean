# Key encapsulation and hybrid encryption

## Key-encapsulation mechanisms

- [Key-encapsulation mechanism](kemscheme.md)
- [Correctness of a key-encapsulation mechanism](correct.md)
- [Adversary against a key-encapsulation mechanism](kemadversary.md)
- [Challenge key of the KEM experiment](challenge-key.md)
- [Left-or-right KEM experiment](kem-exp.md)
- [CPA experiment for key encapsulation](kem-game.md)
- [KEM advantage](kem-advantage.md)
- [KEM advantage as a distinguishing advantage](kem-advantage-eq.md)

## Hybrid encryption

- [Hybrid encryption](hybrid.md)
- [Correctness of hybrid encryption](hybrid-correct.md)
- [KEM adversary from a public-key adversary](kem-reduction.md)
- [Eavesdropper against the data-encapsulation mechanism](dem-reduction.md)
- [The data-encapsulation reduction is an eavesdropper](dem-reduction-query-bounded.md)
- [Intermediate worlds of the hybrid proof](hyb-world.md)
- [The hybrid scheme's experiment is the hybrid world with the real key](pub-cpa-exp-hybrid.md)
- [The KEM reduction's experiment is a hybrid world](kem-exp-kem-reduction.md)
- [The data-encapsulation reduction's experiment is a hybrid world](cpa-exp-dem-reduction.md)
- [Security of hybrid encryption](pub-cpa-advantage-hybrid-le.md)

## The Diffie–Hellman KEM

- [Diffie–Hellman KEM](dh-kem.md)
- [Correctness of the Diffie–Hellman KEM](dh-kem-correct.md)
- [The Diffie–Hellman KEM with the encapsulated key](kem-exp-dh-kem-false.md)
- [The Diffie–Hellman KEM with a uniform key](kem-exp-dh-kem-true.md)
- [The Diffie–Hellman KEM is CPA-secure if DDH is hard](kem-advantage-dh-kem.md)

## The group one-time pad as a DEM, and the ElGamal-style hybrid

- [One-time pad as a data-encapsulation mechanism](otp-dem.md)
- [The one-time-pad data-encapsulation mechanism is correct](otp-dem-correct.md)
- [The one-time pad term vanishes](cpa-advantage-otp-dem-dem-reduction.md)
- [CPA security of the ElGamal-style hybrid scheme](pub-cpa-advantage-dh-hybrid-le.md)

# Specific security experiments as instances of the generic games

## The PRF-MAC

- [MAC from a pseudorandom function](prf-mac.md)
- [The PRF-MAC is correct](prf-mac-correct.md)
- [MAC forger with uniform coins from a coin-indexed forger](to-macforger.md)
- [PRF forgery game equals the MAC forgery experiment of the PRF-MAC](prf-mac-game-eq.md)
- [The PRF-MAC bound](prf-mac-advantage-le.md)
- [The PRF-MAC forgery experiment for arbitrary coins](mac-game-prf-mac-eq-bind.md)
- [The PRF-MAC bound for arbitrary coins](exists-mac-advantage-prf-mac-le.md)
- [PRF-MAC forgery is invariant under relabeling messages along an injection](mac-game-prf-mac-relabel.md)

## PRF encryption

- [PRF-based encryption scheme](prf-enc.md)
- [PRF-based encryption is correct](prf-enc-correct.md)
- [CPA adversary with uniform coins from a coin-indexed adversary](to-cpaadversary.md)
- [Up-front encryption randomness under sequential composition](run-enc-bind.md)
- [Dropping the first entry of the up-front randomness](run-enc-succ.md)
- [Up-front versus fresh randomness](map-uniform-run-enc.md)
- [The fixed-tape PRF-encryption guess as one run](cpa-guess-eq.md)
- [Reordering the CPA sample space](cpa-reorder.md)
- [Up-front and fresh randomness give the same CPA experiment](prf-cpa-game-eq.md)
- [CPA security of PRF-based encryption](prf-cpa-advantage-le.md)

## ElGamal

- [ElGamal eavesdropper as a public-key adversary](to-pub-cpa.md)

## Lamport signatures

- [Lamport one-time signature scheme](lamport.md)
- [Lamport signatures are correct](lamport-correct.md)
- [Lamport one-time forger as a signature forger](to-sig-forger.md)
- [The embedded Lamport forger makes at most one query](to-sig-forger-query-bounded.md)
- [Lamport forgery experiment as a signature-forgery experiment](lamport-forge-game-eq.md)
- [Lamport one-time signature security bound](lamport-sig-advantage-le.md)

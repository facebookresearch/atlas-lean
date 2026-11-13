# Eav Game

The eavesdropping experiment `PubK^eav` (Katz and Lindell, Section 11.2.1) for a
**deterministic** public-key encryption function `Enc : (pk : PK) → M pk → C pk`: a key pair
`k` is drawn from `gen`, the adversary sees the public key `pub k`, the coins `r` and the
challenge bit `b` are uniform, the adversary submits an eligible pair (enforced by
`EavAdversary.eligible`), the challenge is `Enc (pub k) m_b`, and the game outputs whether the
guess equals `b`. Encryption uses no randomness.

Wave 2: migrate to `CSLibExt.Crypto.Framework` games.

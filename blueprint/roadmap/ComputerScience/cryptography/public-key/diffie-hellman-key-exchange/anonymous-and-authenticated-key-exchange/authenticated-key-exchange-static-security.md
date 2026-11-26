# Authenticated key exchange with static corruptions

In an *authenticated key exchange* (AKE) protocol, users hold long-term key pairs registered with their identities. An active adversary controls the network: it creates protocol instances, delivers or modifies messages, may obtain session keys of instances (reveal queries) and the long-term keys of users it statically corrupts in advance. The protocol is *statically secure* if (i) partnered instances of honest users compute the same key and each instance has at most one partner, and (ii) for a fresh test instance (honest, unrevealed, with an unrevealed partner), the adversary distinguishes its session key from a uniform key with negligible advantage.

## Depends on

- [Key-guessing security of anonymous key exchange](key-guessing-security-of-key-exchange.md)
- [Key-exchange eavesdropping experiment](../../security-of-diffie-hellman-key-exchange/ke-game.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.

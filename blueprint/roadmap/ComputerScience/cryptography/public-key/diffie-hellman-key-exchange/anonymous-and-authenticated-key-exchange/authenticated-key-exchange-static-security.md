# Authenticated key exchange with static corruptions

In an *authenticated key exchange* (AKE) protocol with a trusted third party (offline, such as a certificate authority, or online), users register their identities and obtain long-term secret keys, and an instance of a user runs a session-key establishment protocol in a role, left or right, that ends either with abort or with a partner identity and a session key in a key space $K$. *Static security* (Boneh and Shoup, Definition 21.1) compares two experiments. In Experiment 0 the adversary registers honest users, whose long-term keys and instance states it never sees, and corrupt users, by running the registration itself under identities that are never those of honest users; it initializes instances of honest users, delivers messages to them and to the trusted party, and receives every outgoing message and, when an instance finishes, its partner identity and session key. Experiment 1 differs only in the session key handed over: an efficiently computable *partner function*, applied to the communication log, classifies each finishing instance $I$ as *vulnerable* (the adversary receives $I$'s real key, allowed only if $I$'s partner is corrupt), *fresh* (it receives an independent uniform key from $K$, allowed only if $I$'s partner is registered) or *connected* to a finished fresh instance $J$ that is compatible with $I$ (each one's partner identity is the other's user identity and their roles differ) and to which no other instance has connected (it receives $J$'s key); in every other case it receives an error value. The protocol is statically secure if for some such partner function every efficient adversary has negligible advantage $|\Pr[W_0] - \Pr[W_1]|$, where $W_b$ is the event that it outputs $1$ in Experiment $b$. Since the adversary receives every honest session key, there are no reveal or test queries; and since honest users' long-term keys are never revealed, the notion models neither perfect forward secrecy nor HSM security.

## Depends on

- [Key-guessing security of anonymous key exchange](key-guessing-security-of-key-exchange.md)
- [Key-exchange eavesdropping experiment](../../security-of-diffie-hellman-key-exchange/ke-game.md)
- [Efficient adversaries](../../../security-games/asymptotic-security/efficient-adversaries.md)
- [Negligible advantage](../../../security-games/asymptotic-security/negligible-adv.md)
## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023, Section 21.9, Definition 21.1.

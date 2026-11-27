# Needham–Schroeder guarantees weak agreement to the initiator but not to the responder

**Proposition.** In Cortier and Kremer's applied pi model $P^5_{\mathrm{nspk}}$ of the [Needham–Schroeder public-key protocol](../symbolic-protocol-analysis/needham-schroeder-public-key-protocol.md)
(honest agents $a$ and $b$ in any number of sessions, each also willing to talk to the attacker), annotated with the events of their Section 6.3.2, and with an active attacker, the protocol guarantees [aliveness](lowes-hierarchy-of-authentication-properties.md) to both the initiator and the responder and weak agreement to the
initiator, but not weak agreement to the responder: in Lowe's man-in-the-middle attack the responder $b$ accepts a run
with $a$ while $a$ started a run with the attacker.

## Depends on

- [Lowe's hierarchy of authentication properties](lowes-hierarchy-of-authentication-properties.md)
- [The Needham–Schroeder public-key protocol](../symbolic-protocol-analysis/needham-schroeder-public-key-protocol.md)

## Proof depends on

- [Lowe's attack on the Needham–Schroeder public-key protocol](../symbolic-protocol-analysis/lowes-attack-on-needham-schroeder.md)

## Sources

- V. Cortier and S. Kremer, "Formal models and techniques for analyzing security protocols: a tutorial", *Foundations and Trends in Programming Languages* 1(3), 2014, doi:10.1561/2500000001, copy at <https://inria.hal.science/hal-01090874>: Section 6.3.2, the encodings of aliveness and weak agreement for the processes $P^5_{\mathrm{nspk}}$ and $P^6_{\mathrm{nspk}}$ and the discussion of which hold.

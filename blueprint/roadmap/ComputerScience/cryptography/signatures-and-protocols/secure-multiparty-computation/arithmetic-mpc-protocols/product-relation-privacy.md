# Simulation privacy of product-relation verification

In the product-relation verification protocol over $\mathbb{Z}_q$ with $2m < q$ and an honest dealer whose inputs satisfy all product relations, the view of a corrupt $P_1$ (respectively $P_2$), including the challenge point and the other party's shares of $A(r), B(r), C(r)$, can be simulated exactly from that party's own shares alone: the real experiment and the experiment in which the honest party's messages are produced by the simulator have identical output distributions, for every adversary that chooses the shared values subject to the relations.

## Proof sketch

The random $a_0, b_0$ make $A(r)$ and $B(r)$ uniform for every $r \notin \{0, \dots, m\}$, so the honest party's shares of them are uniform given the corrupt party's view, and its share of $C(r)$ is determined by $A(r)B(r)$.

## Depends on

- [Verifying product relations between additive shares](product-relation-verification-protocol.md)

## Sources

- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.

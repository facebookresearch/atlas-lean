# Streams form a complete partial order

For every set $D$, the set $D^\omega$ of [finite and infinite sequences under the prefix order](streams-and-the-prefix-order.md) has the least element $\Lambda$, and every increasing chain $X_1 \sqsubseteq X_2 \sqsubseteq \cdots$ in $D^\omega$ has a least upper bound: the sequence whose finite initial segments are exactly the finite initial segments of the $X_n$, the union of the chain. So $D^\omega$ is a complete partial order, and so is every finite product of such orders, ordered componentwise.

## Depends on

- [Streams and the prefix order](streams-and-the-prefix-order.md)

## Sources

- G. Kahn, "The semantics of a simple language for parallel programming", IFIP Congress 74, 1974; retypeset version read at <https://perso.ensta.fr/~chapoutot/various/kahn_networks.pdf>, Section 2.2.2: "Any increasing chain in $D^\omega$ has a least upper bound ... Hence, $D^\omega$ is a complete partial order".

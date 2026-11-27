# Continuity of the least solution of a Kahn network

The least solution of the system of equations of a [Kahn process network](kahn-process-networks.md), given by [the Kahn principle](kahn-principle.md), is a continuous function of the parameters of the system: of the input streams and of the continuous functions interpreting the processes, ordered pointwise. Consequently a network can itself be used as a process in a larger network, and replacing a subnetwork by a single process that computes the same function of its inputs does not change the histories of the other lines.

## Depends on

- [The Kahn principle](kahn-principle.md)
- [Kahn process networks](kahn-process-networks.md)

## Proof depends on

- [Scott continuity of the least-fixed-point operator](../../../Order/fixed-points-domain-theory/scott-continuous-maps-and-least-fixed-points/lfp-scott-continuous.md)

## Sources

- G. Kahn, "The semantics of a simple language for parallel programming", IFIP Congress 74, 1974; retypeset version read at <https://perso.ensta.fr/~chapoutot/various/kahn_networks.pdf>, Section 3: Property 2 ("Scott") and the discussion of arbitrary interconnection of systems that follows it.

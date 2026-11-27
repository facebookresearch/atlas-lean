# Kernel of the assembled stiffness matrix of a space frame

This node covers the rigid-body kernel of the direct stiffness method. Consider a space frame whose members are straight
Euler-Bernoulli beam elements with positive axial, torsional and two bending stiffnesses, rigidly connected at nodes, each node having three
translational and three rotational degrees of freedom. Let $K = \sum_e T_e^{\mathsf T} k_e T_e$ be the assembled stiffness matrix, where $k_e$ is
the element stiffness matrix in local axes and $T_e$ the transformation by the member's direction cosines. If the frame is connected, then $K$
is symmetric positive semidefinite and its kernel is exactly the six-dimensional space of nodal displacements induced by infinitesimal rigid
motions $u(x) = c + \omega \times x$ of the whole frame. Consequently any support conditions that admit no nonzero infinitesimal rigid motion make
the reduced stiffness matrix positive definite.

## Depends on

- [Supported virtual work](../pin-jointed-trusses/supported-virtual-work-iff.md)

## Expansion

A good expansion states the element stiffness matrix and its kernel (the rigid motions of one member), proves that the
transformation preserves that kernel, and then shows by induction along a spanning tree of the frame that a displacement with zero strain
energy is one rigid motion. Nonzero modal consumers and member releases are separate nodes.

## Sources

- T. H. G. Megson, *Aircraft Structures for Engineering Students*, 5th edition, Butterworth-Heinemann, 2012, for the matrix stiffness method.

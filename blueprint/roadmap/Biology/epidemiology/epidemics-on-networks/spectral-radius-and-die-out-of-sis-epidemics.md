# Spectral radius and die-out of SIS epidemics on graphs

This page covers a research target from Ganesh, Massoulié and Towsley (2005). For the continuous-time SIS process on a finite graph $G$ with $n$ vertices and adjacency matrix $A$, in which each infected vertex infects each neighbour at rate $\beta$ and recovers at rate $\delta$, the target is the pair of results:

- **fast die-out:** if $\beta / \delta < 1/\rho(A)$, with $\rho(A)$ the spectral radius, the expected extinction time is of order $\log n$;
- **slow die-out:** if $\beta / \delta$ exceeds $1/\eta(G)$, with $\eta(G)$ a generalized isoperimetric constant of the graph, the extinction time is exponentially long in a power of $n$.

## Expansion

Fix from the source the initial condition, the constants in both bounds and the definition of $\eta(G)$, state the two results as theorems, and prove them.

Prerequisites:

- [Threshold theorem for the SIS model](../sis-epidemic-model/deriv-infected-pos-iff.md)

## Sources

- A. Ganesh, L. Massoulié and D. Towsley, The effect of network topology on the spread of epidemics, in *Proceedings of IEEE INFOCOM 2005*, vol. 2, 1455–1466, <https://doi.org/10.1109/INFCOM.2005.1498374>.

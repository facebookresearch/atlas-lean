# The Kahn principle

The system of equations $\Sigma_P = \{ X_i = \tau_i(X_1, \dots, X_n) \mid 1 \le i \le n \}$ of a [Kahn process network](kahn-process-networks.md), whose terms $\tau_i$ are built from continuous operators, has a least solution $(Y_1, \dots, Y_n)$ in the [complete partial order of streams](streams-form-a-complete-partial-order.md), and it is the limit of the iterates

$$X_i^0 = \Lambda, \qquad X_i^{j+1} = \tau_i(X_1^j, \dots, X_n^j).$$

This least solution is taken as the histories of the lines of the network, so the histories are a function of the input streams.

## Depends on

- [Kahn process networks](kahn-process-networks.md)
- [Streams form a complete partial order](streams-form-a-complete-partial-order.md)

## Proof depends on

- [The least fixed point is a fixed point](../../../Order/fixed-points-domain-theory/scott-continuous-maps-and-least-fixed-points/lfp-eq.md)
- [The least fixed point lies below every prefixed point](../../../Order/fixed-points-domain-theory/scott-continuous-maps-and-least-fixed-points/lfp-le.md)

## Sources

- G. Kahn, "The semantics of a simple language for parallel programming", IFIP Congress 74, 1974; retypeset version read at <https://perso.ensta.fr/~chapoutot/various/kahn_networks.pdf>, Section 3: the system $\Sigma_P$, Property 1 ("Kleene") and the choice of its least solution as the histories of the lines.

# Dispute wheels

A *dispute wheel* of size $k$ in an instance of the [stable paths problem](the-stable-paths-problem.md) is a sequence of nodes $u_0, \dots, u_{k-1}$ with nonempty paths $Q_0, \dots, Q_{k-1}$ and $R_0, \dots, R_{k-1}$ such that, for each $i$ (indices modulo $k$):

1. $R_i$ is a path from $u_i$ to $u_{i+1}$;
2. $Q_i \in \mathcal P^{u_i}$;
3. $R_i Q_{i+1} \in \mathcal P^{u_i}$;
4. $\lambda^{u_i}(Q_i) \le \lambda^{u_i}(R_i Q_{i+1})$.

Each $u_i$ weakly prefers reaching the origin through its neighbour on the wheel to its own spoke. Since permitted paths are simple, $k \ge 2$; nodes may repeat. The wheel is *minimal* if for each $i$ either $R_i R_{i+1} Q_{i+2}$ is not permitted at $u_i$ or $\lambda^{u_i}(R_i R_{i+1} Q_{i+2}) \le \lambda^{u_i}(R_i Q_{i+1})$; every dispute wheel of size $2$ is minimal. DISAGREE and BAD GADGET have dispute wheels.

## Depends on

- [The stable paths problem](the-stable-paths-problem.md)

## Sources

- T. G. Griffin, F. B. Shepherd and G. Wilfong, "The stable paths problem and interdomain routing", *IEEE/ACM Transactions on Networking* 10(2):232–243, 2002, Sections V.B and V.C (the definition of dispute wheels, Fig. 9, sub-wheels and minimal dispute wheels).

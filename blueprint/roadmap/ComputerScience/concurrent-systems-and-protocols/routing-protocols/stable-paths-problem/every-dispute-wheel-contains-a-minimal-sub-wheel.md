# Every dispute wheel contains a minimal sub-wheel

Let $u_0, \dots, u_{k-1}$ with spokes $Q_i$ and rims $R_i$ (indices modulo $k$) be a [dispute wheel](../../../../GameTheory/noncooperative-games/selfish-routing-and-the-price-of-anarchy/interdomain-routing-games/stable-paths-problem-and-dispute-wheels.md) of an instance of the stable paths problem, with $\lambda^{u}$ the ranking at node $u$, in the weak form of Griffin, Shepherd and Wilfong's condition (4): $R_i Q_{i+1}$ is permitted at $u_i$ and $\lambda^{u_i}(Q_i) \le \lambda^{u_i}(R_i Q_{i+1})$, so ties between a spoke and the detour are allowed (they can occur under the same-next-hop tie rule). The wheel is *minimal* if for each $i$ either $R_i R_{i+1} Q_{i+2}$ is not permitted at $u_i$ or $\lambda^{u_i}(R_i R_{i+1} Q_{i+2}) \le \lambda^{u_i}(R_i Q_{i+1})$; a wheel of size $2$ is minimal, since $R_i R_{i+1} Q_i$ returns to $u_i$ and is not simple. Suppressing index $i$ removes $u_i$ and $Q_i$ and replaces $R_{i-1}$ and $R_i$ by $R_{i-1}R_i$; a *sub-wheel* is a dispute wheel obtained by a sequence of such suppressions. Every dispute wheel contains a minimal sub-wheel: if $R_i R_{i+1} Q_{i+2}$ is permitted at $u_i$ and $\lambda^{u_i}(R_i Q_{i+1}) < \lambda^{u_i}(R_i R_{i+1} Q_{i+2})$ for some $i$, then $\lambda^{u_i}(Q_i) \le \lambda^{u_i}(R_i Q_{i+1}) < \lambda^{u_i}(R_i R_{i+1} Q_{i+2})$, so suppressing index $i + 1$ gives a smaller dispute wheel, the weak condition at $u_i$ holding with strict inequality, and the process stops at a minimal one.

## Depends on

- [Stable paths problem and dispute wheels](../../../../GameTheory/noncooperative-games/selfish-routing-and-the-price-of-anarchy/interdomain-routing-games/stable-paths-problem-and-dispute-wheels.md)

## Sources

- T. G. Griffin, F. B. Shepherd and G. Wilfong, "The stable paths problem and interdomain routing", *IEEE/ACM Transactions on Networking* 10(2):232–243, 2002, Section V.C, Lemma V.2 with its proof.

# Every dispute wheel contains a minimal sub-wheel

Suppressing index $i$ of a [dispute wheel](dispute-wheels.md) removes $u_i$ and $Q_i$ and replaces $R_{i-1}$ and $R_i$ by $R_{i-1}R_i$; a *sub-wheel* is a dispute wheel obtained by a sequence of such suppressions. Every dispute wheel contains a minimal sub-wheel: if $\lambda^{u_i}(R_i Q_{i+1}) < \lambda^{u_i}(R_i R_{i+1} Q_{i+2})$ for some $i$, suppressing index $i + 1$ gives a smaller dispute wheel, and the process stops at a minimal one.

## Depends on

- [Dispute wheels](dispute-wheels.md)

## Sources

- T. G. Griffin, F. B. Shepherd and G. Wilfong, "The stable paths problem and interdomain routing", *IEEE/ACM Transactions on Networking* 10(2):232–243, 2002, Section V.C, Lemma V.2 with its proof.

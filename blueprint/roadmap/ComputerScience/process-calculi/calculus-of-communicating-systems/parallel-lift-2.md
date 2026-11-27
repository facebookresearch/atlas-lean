# Lifting two relations through parallel composition in recursive CCS

Given two relations $R$ and $S$ on recursive CCS processes (built from $0$ and process constants by action prefix, choice, parallel composition, restriction by a finite list of channel names and relabelling by a finite relabelling table), their parallel lift is the relation that relates $U$ to $V$ exactly when $R(U, V)$ holds, or $S(U, V)$ holds, or $U = P_1 \mid Q_1$ and $V = P_2 \mid Q_2$ for processes with $R(P_1, P_2)$ and $S(Q_1, Q_2)$, where $\mid$ is parallel composition.

## Sources

- Robin Milner, *Communication and Concurrency*, Prentice Hall, 1989, Chapter 4, ISBN 978-0-13-115007-2.

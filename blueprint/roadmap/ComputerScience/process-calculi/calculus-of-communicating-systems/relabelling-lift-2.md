# Lifting a relation through a relabelling in recursive CCS

Given a finite relabelling $f$ and a relation $R$ on recursive CCS processes (built from $0$ and process constants by action prefix, choice, parallel composition, restriction by a finite list of channel names and relabelling by a finite relabelling table), the lifted relation relates $U$ to $V$ exactly when $R(U, V)$ holds, or $U = P[f]$ and $V = Q[f]$ for processes $P$ and $Q$ with $R(P, Q)$, where $[f]$ is relabelling by $f$.

## Sources

- Robin Milner, *Communication and Concurrency*, Prentice Hall, 1989, Chapter 4, ISBN 978-0-13-115007-2.

# Scalar clocks are incomplete and vector clocks need n dimensions

Lamport scalar clocks are strictly monotone along happens-before, and breaking ties by process identifier yields a strict total order extending happens-before; but for at least two processes some execution's causal order embeds into no linear order in a way characterizing causality. More strongly, for $n \ge 2$ processes there is a finite unicast execution (a crown) such that any characterization of happens-before by coordinatewise comparison of timestamps in $\alpha^d$, for any linear order $\alpha$, requires $d \ge n$; so Mattern–Fidge vector clocks of dimension $n$ are optimal.

## Proof sketch

Construct $n$ events $a_p$ and $b_p$ with $a_p$ concurrent to $b_{p+1}$ but $a_p$ before $b_q$ for all other $q$ (a crown of order dimension $n$); a $d$-dimensional coordinatewise embedding would realize this crown, which requires $d \ge n$.

## Depends on

- [Vector clocks characterize happened-before](../../vector-clocks/happens-before-iff-lt.md)
- [Lamport timestamps](../../lamport-clocks/timestamps.md)
- [Happened-before](../../lamport-clocks/happens-before.md)

## Sources

- Bernadette Charron-Bost, "Concerning the Size of Logical Clocks in Distributed Systems", Information Processing Letters, 1991.
- Leslie Lamport, "Time, Clocks, and the Ordering of Events in a Distributed System", Communications of the ACM, 1978.
- Friedemann Mattern, "Virtual Time and Global States of Distributed Systems", Parallel and Distributed Algorithms, North-Holland, 1989.
- Colin J. Fidge, "Timestamps in Message-Passing Systems That Preserve the Partial Ordering", Proceedings of the 11th Australian Computer Science Conference, 1988.

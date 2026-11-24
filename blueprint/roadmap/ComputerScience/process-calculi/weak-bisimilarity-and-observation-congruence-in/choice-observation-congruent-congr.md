# Choice preserves observation congruence in static CCS

Let the channel names form a type with decidable equality, and consider the static CCS processes (prefix by a CCS label, choice, parallel composition with communication, restriction $P \setminus L$ by a finite list $L$ of names, and relabelling $P[f]$ by a finite relabelling $f$) with the transitions of static CCS. For all processes $P_1, P_2, Q_1, Q_2$: if $P_1$ and $P_2$ are observation congruent (rooted weakly bisimilar) and $Q_1$ and $Q_2$ are observation congruent, then $P_1 + Q_1$ and $P_2 + Q_2$ are observation congruent.

## Sources

- Robin Milner, *Communication and Concurrency*, Prentice Hall, 1989, Chapter 5 (ISBN 978-0-13-115007-2).

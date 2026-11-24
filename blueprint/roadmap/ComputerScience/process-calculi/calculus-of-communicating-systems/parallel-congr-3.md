# Parallel composition preserves strong bisimilarity in static CCS

Let the channel names form a type with decidable equality. For all static CCS processes (finite CCS processes built from $0$ by action prefix, choice, parallel composition, restriction by a finite list of channel names and relabelling by a finite relabelling table) $P_1, P_2, Q_1, Q_2$: if $P_1$ and $P_2$ are strongly bisimilar in the labelled transition system of static CCS, and $Q_1$ and $Q_2$ are strongly bisimilar there, then the parallel compositions $P_1 \mid Q_1$ and $P_2 \mid Q_2$ are strongly bisimilar there. Transitions of a parallel composition include the silent synchronization of complementary actions of its two components.

## Sources

- Robin Milner, *Communication and Concurrency*, Prentice Hall, 1989, Chapters 2–3, ISBN 978-0-13-115007-2.

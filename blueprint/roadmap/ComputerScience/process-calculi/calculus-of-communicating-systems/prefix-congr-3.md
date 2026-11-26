# Prefix preserves strong bisimilarity in static CCS

Let the channel names form a type with decidable equality. For every CCS action $\alpha$ (the silent action $\tau$, an input or an output) and all static CCS processes (finite CCS processes built from $0$ by action prefix, choice, parallel composition, restriction by a finite list of channel names and relabelling by a finite relabelling table) $P$ and $Q$: if $P$ and $Q$ are strongly bisimilar in the labelled transition system of static CCS, then the prefixed processes $\alpha.P$ and $\alpha.Q$ are strongly bisimilar there as well.

## Sources

- Robin Milner, *Communication and Concurrency*, Prentice Hall, 1989, Chapters 2–3, ISBN 978-0-13-115007-2.

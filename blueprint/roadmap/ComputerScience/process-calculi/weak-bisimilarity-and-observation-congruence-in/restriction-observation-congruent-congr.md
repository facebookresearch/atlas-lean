# Restriction preserves observation congruence

Let the channel names form a type with decidable equality, and consider the static CCS processes (prefix by a CCS label, choice, parallel composition with communication, restriction $P \setminus L$ by a finite list $L$ of names, and relabelling $P[f]$ by a finite relabelling $f$) with the transitions of static CCS. For every finite list $L$ of names and all processes $P$, $Q$: if $P$ and $Q$ are observation congruent (rooted weakly bisimilar), then so are $P \setminus L$ and $Q \setminus L$.

## Sources

- Robin Milner, *Communication and Concurrency*, Prentice Hall, 1989, Chapter 5 (ISBN 978-0-13-115007-2).

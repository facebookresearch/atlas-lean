# A silent prefix is invisible to weak bisimilarity in static CCS

Let the channel names form a type with decidable equality, and consider the static CCS processes (prefix by a CCS label, choice, parallel composition with communication, restriction $P \setminus L$ by a finite list $L$ of names, and relabelling $P[f]$ by a finite relabelling $f$) with the transitions of static CCS. For every process $P$, the silent prefix $\tau.P$ is weakly bisimilar to $P$: some bisimulation of the saturated system, whose transitions are the weak transitions, relates $\tau.P$ to $P$.

## Sources

- Robin Milner, *Communication and Concurrency*, Prentice Hall, 1989, Chapter 5 (ISBN 978-0-13-115007-2).

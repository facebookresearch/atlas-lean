# A criterion for the reflexive closure of a relation to be a strong bisimulation in static CCS

Let the channel names form a type with decidable equality. Let $E$ be a relation on static CCS processes (finite CCS processes built from $0$ by action prefix, choice, parallel composition, restriction by a finite list of channel names and relabelling by a finite relabelling table), and write $P \xrightarrow{\alpha} P'$ for the transitions of static CCS. Suppose that:

- whenever $E(P, Q)$ and $P \xrightarrow{\alpha} P'$, there is $Q'$ with $Q \xrightarrow{\alpha} Q'$ such that $P' = Q'$ or $E(P', Q')$;
- whenever $E(P, Q)$ and $Q \xrightarrow{\alpha} Q'$, there is $P'$ with $P \xrightarrow{\alpha} P'$ such that $P' = Q'$ or $E(P', Q')$.

Then the reflexive closure of $E$, which relates $P$ to $Q$ when $P = Q$ or $E(P, Q)$, is a strong bisimulation on the labelled transition system of static CCS.

## Sources

- Robin Milner, *Communication and Concurrency*, Prentice Hall, 1989, Chapters 2–3, ISBN 978-0-13-115007-2.

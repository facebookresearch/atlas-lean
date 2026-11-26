# Relabelling by the empty table is the identity up to strong bisimilarity

Let the channel names form a type with decidable equality. Let $f_\emptyset$ be the relabelling with no entries, which sends the input on every channel $a$ to the input on $a$ and the output on $a$ to the output on $a$. For every static CCS process $P$, the relabelling $P[f_\emptyset]$ is strongly bisimilar in the labelled transition system of static CCS to $P$.

## Sources

- Robin Milner, *Communication and Concurrency*, Prentice Hall, 1989, Chapters 2–3, ISBN 978-0-13-115007-2.

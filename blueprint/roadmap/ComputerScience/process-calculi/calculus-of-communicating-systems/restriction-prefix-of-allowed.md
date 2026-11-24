# A permitted prefix moves out of a restriction

Let the channel names form a type with decidable equality. Let $L$ be a finite list of channel names and $\alpha$ a CCS action permitted by $L$, that is, $\alpha$ is the silent action $\tau$ or an input or output on a channel not in $L$. For every static CCS process $P$, the process $(\alpha.P) \setminus L$ is strongly bisimilar in the labelled transition system of static CCS to $\alpha.(P \setminus L)$.

## Sources

- Robin Milner, *Communication and Concurrency*, Prentice Hall, 1989, Chapters 2–3, ISBN 978-0-13-115007-2.

# Relabelling a prefixed process relabels its prefix

Let the channel names form a type with decidable equality. For every finite relabelling $f$, every CCS action $\alpha$ and every static CCS process $P$, the process $(\alpha.P)[f]$ is strongly bisimilar in the labelled transition system of static CCS to $f(\alpha).(P[f])$. Here $f(\tau) = \tau$, the input on a channel $a$ is sent to the visible label that the table $f$ assigns to $a$ (the first entry for $a$, and the input on $a$ when there is none), and the output on $a$ is sent to the complement of that label.

## Sources

- Robin Milner, *Communication and Concurrency*, Prentice Hall, 1989, Chapters 2–3, ISBN 978-0-13-115007-2.

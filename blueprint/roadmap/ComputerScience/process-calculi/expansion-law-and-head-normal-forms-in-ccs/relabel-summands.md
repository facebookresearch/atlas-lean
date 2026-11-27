# Relabelling a list of summands

Let the channel names form a type with decidable equality. Given a finite relabelling $f$ and a list $s$ of summands, each a CCS action paired with a static CCS process, the relabelled list replaces each entry $(\alpha, P)$ of $s$ with $(f(\alpha), P[f])$, keeping the order. Here $f(\tau) = \tau$, the input on a channel $a$ goes to the visible label that $f$ assigns to $a$, and the output on $a$ goes to the complement of that label.

## Sources

- Robin Milner, *Communication and Concurrency*, Chapters 2–3.

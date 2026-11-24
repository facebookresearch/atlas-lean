# Restrictions by lists with the same members are strongly bisimilar

Let the channel names form a type with decidable equality. Let $L_1$ and $L_2$ be finite lists of channel names with the same members, that is, every name $a$ satisfies $a \in L_1$ if and only if $a \in L_2$. Then for every static CCS process $P$, the restrictions $P \setminus L_1$ and $P \setminus L_2$ are strongly bisimilar in the labelled transition system of static CCS. In particular, the order and the repetitions of names in a restriction list do not matter.

## Sources

- Robin Milner, *Communication and Concurrency*, Prentice Hall, 1989, Chapters 2–3, ISBN 978-0-13-115007-2.

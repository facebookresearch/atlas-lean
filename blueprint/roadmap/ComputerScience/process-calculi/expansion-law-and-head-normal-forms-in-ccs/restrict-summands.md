# Restricting a list of summands

Let the channel names form a type with decidable equality. Given a finite list $L$ of channel names and a list $s$ of summands, each a CCS action paired with a static CCS process, the restricted list is obtained from $s$ by replacing each entry $(\alpha, P)$ whose action is permitted by $L$ with $(\alpha, P \setminus L)$ and deleting each entry whose action is not permitted, keeping the order. An action is permitted by $L$ when it is the silent action $\tau$ or an input or output on a channel not in $L$.

## Sources

- Robin Milner, *Communication and Concurrency*, Chapters 2–3.

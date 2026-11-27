# All synchronization summands of two finite sums

Let the channel names form a type with decidable equality. Given two lists $s$ and $t$ of summands, each a CCS action paired with a static CCS process, their synchronization moves are the concatenation, over the entries $(\alpha, P)$ of $s$ in order, of the synchronizations of $(\alpha, P)$ with $t$. Thus the list contains one entry $(\tau, P \mid Q)$ for each pair of an entry $(\alpha, P)$ of $s$ and an entry $(\beta, Q)$ of $t$ with $\alpha$ and $\beta$ complementary, ordered first by the position in $s$ and then by the position in $t$.

## Sources

- Robin Milner, *Communication and Concurrency*, Prentice Hall, 1989, Chapter 3, ISBN 978-0-13-115007-2.

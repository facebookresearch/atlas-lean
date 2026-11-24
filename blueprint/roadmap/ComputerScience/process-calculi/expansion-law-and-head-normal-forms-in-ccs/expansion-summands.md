# Summands of the expansion of a parallel composition of two finite sums

Let the channel names form a type with decidable equality. For a list $s$ of summands (pairs $(\alpha, P)$ of a CCS action and a static CCS process), $\Sigma s$ denotes the right-associated finite choice $\alpha_1.P_1 + (\alpha_2.P_2 + (\cdots + (\alpha_n.P_n + 0)))$ of its entries, with $\Sigma [\,] = 0$. For lists $s$ and $t$ of summands, the expansion summands are the concatenation of three lists, in this order: the entry $(\alpha, P \mid \Sigma t)$ for each entry $(\alpha, P)$ of $s$; the entry $(\beta, \Sigma s \mid Q)$ for each entry $(\beta, Q)$ of $t$; and the entry $(\tau, P \mid Q)$ for each pair of an entry $(\alpha, P)$ of $s$ and an entry $(\beta, Q)$ of $t$ whose actions are complementary, ordered first by the position in $s$ and then by the position in $t$.

## Sources

- Robin Milner, *Communication and Concurrency*, Prentice Hall, 1989, Chapter 3, ISBN 978-0-13-115007-2.

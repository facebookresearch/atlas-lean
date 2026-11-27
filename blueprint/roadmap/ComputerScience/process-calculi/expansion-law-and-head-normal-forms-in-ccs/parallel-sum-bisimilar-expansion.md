# Expansion law for the parallel composition of two finite sums

Let the channel names form a type with decidable equality. For a list $s$ of summands (pairs $(\alpha, P)$ of a CCS action and a static CCS process), $\Sigma s$ denotes the right-associated finite choice $\alpha_1.P_1 + (\alpha_2.P_2 + (\cdots + (\alpha_n.P_n + 0)))$ of its entries, with $\Sigma [\,] = 0$. For all lists $s$ and $t$ of summands, the parallel composition $\Sigma s \mid \Sigma t$ is strongly bisimilar, in the labelled transition system of static CCS, to the expansion of $s$ and $t$: the finite sum of $\alpha.(P \mid \Sigma t)$ over the entries $(\alpha, P)$ of $s$, of $\beta.(\Sigma s \mid Q)$ over the entries $(\beta, Q)$ of $t$, and of $\tau.(P \mid Q)$ over the pairs of entries $(\alpha, P)$ of $s$ and $(\beta, Q)$ of $t$ with $\alpha$ and $\beta$ complementary.

## Sources

- Robin Milner, *Communication and Concurrency*, Prentice Hall, 1989, Chapter 3, ISBN 978-0-13-115007-2.

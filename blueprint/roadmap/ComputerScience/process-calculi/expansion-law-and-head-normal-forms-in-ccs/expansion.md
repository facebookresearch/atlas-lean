# Expansion of a parallel composition of two finite sums

Let the channel names form a type with decidable equality. For a list $s$ of summands (pairs $(\alpha, P)$ of a CCS action and a static CCS process), $\Sigma s$ denotes the right-associated finite choice $\alpha_1.P_1 + (\alpha_2.P_2 + (\cdots + (\alpha_n.P_n + 0)))$ of its entries, with $\Sigma [\,] = 0$. For lists $s$ and $t$ of summands, the expansion of $s$ and $t$ is the finite sum $\Sigma u$ of their expansion summands $u$: the summands $\alpha.(P \mid \Sigma t)$ for the entries $(\alpha, P)$ of $s$, then $\beta.(\Sigma s \mid Q)$ for the entries $(\beta, Q)$ of $t$, then $\tau.(P \mid Q)$ for each pair of entries $(\alpha, P)$ of $s$ and $(\beta, Q)$ of $t$ with $\alpha$ and $\beta$ complementary.

## Sources

- Robin Milner, *Communication and Concurrency*, Prentice Hall, 1989, Chapter 3, ISBN 978-0-13-115007-2.

# The sum of a concatenation is the choice of the two sums

Let the channel names form a type with decidable equality. For a list $s$ of summands (pairs $(\alpha, P)$ of a CCS action and a static CCS process), $\Sigma s$ denotes the right-associated finite choice $\alpha_1.P_1 + (\alpha_2.P_2 + (\cdots + (\alpha_n.P_n + 0)))$ of its entries, with $\Sigma [\,] = 0$. For all lists $s$ and $t$ of summands, the finite sum $\Sigma (s \mathbin{+\!\!+} t)$ of their concatenation is strongly bisimilar, in the labelled transition system of static CCS, to the choice $\Sigma s + \Sigma t$.

## Sources

- Robin Milner, *Communication and Concurrency*, Chapters 2–3.

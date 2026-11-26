# A one-summand sum is strongly bisimilar to the prefixed process

Let the channel names form a type with decidable equality. For a list $s$ of summands (pairs $(\alpha, P)$ of a CCS action and a static CCS process), $\Sigma s$ denotes the right-associated finite choice $\alpha_1.P_1 + (\alpha_2.P_2 + (\cdots + (\alpha_n.P_n + 0)))$ of its entries, with $\Sigma [\,] = 0$. For every CCS action $\alpha$ and every static CCS process $P$, the one-entry sum $\Sigma [(\alpha, P)] = \alpha.P + 0$ is strongly bisimilar, in the labelled transition system of static CCS, to $\alpha.P$.

## Sources

- Robin Milner, *Communication and Concurrency*, Chapters 2–3.

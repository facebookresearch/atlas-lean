# Restriction of a finite sum keeps exactly its permitted summands

Let the channel names form a type with decidable equality. For a list $s$ of summands (pairs $(\alpha, P)$ of a CCS action and a static CCS process), $\Sigma s$ denotes the right-associated finite choice $\alpha_1.P_1 + (\alpha_2.P_2 + (\cdots + (\alpha_n.P_n + 0)))$ of its entries, with $\Sigma [\,] = 0$. For every finite list $L$ of channel names and every list $s$ of summands, the restriction $(\Sigma s) \setminus L$ is strongly bisimilar, in the labelled transition system of static CCS, to $\Sigma s'$, where $s'$ is obtained from $s$ by replacing each entry $(\alpha, P)$ with $\alpha$ permitted by $L$ by $(\alpha, P \setminus L)$ and deleting the other entries.

## Sources

- Robin Milner, *Communication and Concurrency*, Chapters 2–3.

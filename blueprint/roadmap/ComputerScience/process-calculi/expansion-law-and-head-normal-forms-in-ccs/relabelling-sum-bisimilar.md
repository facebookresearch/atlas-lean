# Relabelling of a finite sum relabels each summand

Let the channel names form a type with decidable equality. For a list $s$ of summands (pairs $(\alpha, P)$ of a CCS action and a static CCS process), $\Sigma s$ denotes the right-associated finite choice $\alpha_1.P_1 + (\alpha_2.P_2 + (\cdots + (\alpha_n.P_n + 0)))$ of its entries, with $\Sigma [\,] = 0$. For every finite relabelling $f$ and every list $s$ of summands, the relabelling $(\Sigma s)[f]$ is strongly bisimilar, in the labelled transition system of static CCS, to $\Sigma s'$, where $s'$ replaces each entry $(\alpha, P)$ of $s$ with $(f(\alpha), P[f])$ and $f$ acts on actions as in relabelling (fixing $\tau$, an output going to the complement of the image of the corresponding input).

## Sources

- Robin Milner, *Communication and Concurrency*, Chapters 2–3.

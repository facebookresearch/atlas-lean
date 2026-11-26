# Actions enabled by a finite sum

Let the channel names form a type with decidable equality. For a list $s$ of summands (pairs $(\alpha, P)$ of a CCS action and a static CCS process), $\Sigma s$ denotes the right-associated finite choice $\alpha_1.P_1 + (\alpha_2.P_2 + (\cdots + (\alpha_n.P_n + 0)))$ of its entries, with $\Sigma [\,] = 0$. For every list $s$ of summands and every CCS action $\alpha$, the process $\Sigma s$ has a transition labelled $\alpha$ in static CCS if and only if $s$ has an entry $(\alpha, P)$ for some process $P$.

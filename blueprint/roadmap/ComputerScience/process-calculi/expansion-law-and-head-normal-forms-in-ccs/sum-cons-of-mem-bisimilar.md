# Adding a summand that is already present preserves strong bisimilarity

Let the channel names form a type with decidable equality. For a list $s$ of summands (pairs $(\alpha, P)$ of a CCS action and a static CCS process), $\Sigma s$ denotes the right-associated finite choice $\alpha_1.P_1 + (\alpha_2.P_2 + (\cdots + (\alpha_n.P_n + 0)))$ of its entries, with $\Sigma [\,] = 0$. If a summand $(\alpha, P)$ is an entry of the list $s$, then $\Sigma ((\alpha, P) :: s) = \alpha.P + \Sigma s$ is strongly bisimilar in the labelled transition system of static CCS to $\Sigma s$.

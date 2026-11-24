# Reversing the summands of a finite sum preserves strong bisimilarity

Let the channel names form a type with decidable equality. For a list $s$ of summands (pairs $(\alpha, P)$ of a CCS action and a static CCS process), $\Sigma s$ denotes the right-associated finite choice $\alpha_1.P_1 + (\alpha_2.P_2 + (\cdots + (\alpha_n.P_n + 0)))$ of its entries, with $\Sigma [\,] = 0$. For every list $s$ of summands, the sum $\Sigma(\operatorname{reverse} s)$ of the reversed list is strongly bisimilar in the labelled transition system of static CCS to $\Sigma s$.

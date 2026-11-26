# Swapping two blocks of summands preserves strong bisimilarity

Let the channel names form a type with decidable equality. For a list $s$ of summands (pairs $(\alpha, P)$ of a CCS action and a static CCS process), $\Sigma s$ denotes the right-associated finite choice $\alpha_1.P_1 + (\alpha_2.P_2 + (\cdots + (\alpha_n.P_n + 0)))$ of its entries, with $\Sigma [\,] = 0$. For all lists $s$ and $t$ of summands, the sums $\Sigma (s \mathbin{+\!\!+} t)$ and $\Sigma (t \mathbin{+\!\!+} s)$ of the two concatenations are strongly bisimilar in the labelled transition system of static CCS.

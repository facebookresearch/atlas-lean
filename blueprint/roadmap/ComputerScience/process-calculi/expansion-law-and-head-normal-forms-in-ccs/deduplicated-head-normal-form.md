# Deduplicated head normal form of a static CCS process

Let the channel names form a type with decidable equality. The deduplicated head normal form of a static CCS process $P$ is the finite sum $\Sigma d(P)$ of its deduplicated head summands $d(P)$ (its head summands with repeated entries removed, keeping last occurrences), where $\Sigma [(\alpha_1, P_1), \dots, (\alpha_n, P_n)] = \alpha_1.P_1 + (\cdots + (\alpha_n.P_n + 0))$ and $\Sigma [\,] = 0$.

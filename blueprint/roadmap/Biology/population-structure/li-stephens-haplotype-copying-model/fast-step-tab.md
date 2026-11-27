# Tabulated O(K) forward step

Let $R$ be a field and $\rho, \varepsilon \in R$. For a [site observation](obs.md) $o$ and a vector $v \in R^K$, the tabulated step first computes the total $S = \sum_j v_j$ once and then returns the vector with entries $e_\varepsilon(k, o)\bigl((1 - \rho) v_k + \rho S / K\bigr)$ for $k = 1, \dots, K$; it equals the [collapsed forward step](fast-step.md) and costs $O(K)$ field operations.

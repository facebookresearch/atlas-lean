# Tabulated O(K) forward variables

Let $R$ be a field, $\rho, \varepsilon \in R$ and $y$ a sequence of [site observations](obs.md). The tabulated forward vectors are the vector $\bigl(\frac1K e_\varepsilon(k, y_0)\bigr)_k$ at site $0$ and, at site $t + 1$, the [tabulated step](fast-step-tab.md) applied to $y_{t+1}$ and the vector at site $t$: $t + 1$ sites cost $O(tK)$ field operations.

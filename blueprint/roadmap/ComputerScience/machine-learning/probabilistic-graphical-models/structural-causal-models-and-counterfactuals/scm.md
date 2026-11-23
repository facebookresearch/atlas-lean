# Markovian structural causal model

**Markovian structural causal model** (Pearl 1995, eq. (3); Pearl, *Statistics Surveys*
2009, §3.2): a model with endogenous variables valued in a set $\alpha$ on the nodes
$0, \dots, n - 1$ in a topological order, consists of, for each node $k$, a set
$\mathrm{pa}(k) \subseteq \{0, \dots, k - 1\}$ of parents, a finitely supported law $\pi_k$ on a
set $\beta$ for its disturbance $U_k$ (the disturbances are mutually independent), and a
structural equation $X_k = f_k(X_{\mathrm{pa}(k)}, U_k)$ given by a map
$f_k : \alpha^{\mathrm{pa}(k)} \times \beta \to \alpha$.

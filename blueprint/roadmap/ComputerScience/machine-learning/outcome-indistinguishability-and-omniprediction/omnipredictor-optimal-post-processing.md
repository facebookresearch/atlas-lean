# Optimal post-processing is the identity for proper losses and a threshold for cost-sensitive losses

Let $\ell$ be a loss and $k_\ell(v) \in \arg\min_t \mathbb{E}_{y \sim \mathrm{Ber}(v)}[\ell(t, y)]$ its optimal action for forecast $v$. If $\ell$ is a proper loss (a proper scoring rule, such as squared loss or log loss), then $k_\ell(v) = v$ is optimal; for the cost-sensitive classification loss on the action set $t \in \{0,1\}$, $\ell(t,y) = c\,\mathbf{1}[t = 1, y = 0] + (1-c)\,\mathbf{1}[t = 0, y = 1]$ with $c \in (0,1)$, the optimal action is the threshold rule $k_\ell(v) = \mathbf{1}[v \ge c]$ (the minimum is over $\{0,1\}$ only: extended to real actions by the same formula, every $t \notin \{0,1\}$ would have loss $0$; at $v = c$ both actions cost $c(1-c)$ and the rule picks $1$); and for convex losses with $\ell(t,1)-\ell(t,0)$ nonincreasing in $t$, $k_\ell$ can be chosen nondecreasing in $v$. In all cases $k_\ell$ is univariate and data-independent, which is what allows a single omnipredictor to serve every loss.

## Proof sketch

Properness is exactly the statement that reporting the true probability minimizes expected loss under $\mathrm{Ber}(v)$. For the cost-sensitive loss, predicting $1$ costs $c(1-v)$ and predicting $0$ costs $(1-c)v$, which compare at $v = c$. For convex $\ell(\cdot, y)$, the expected loss $v\ell(t,1) + (1-v)\ell(t,0)$ has submodular dependence on $(t, v)$ when $\ell(t,1) - \ell(t,0)$ is nonincreasing in $t$, giving monotone minimizers by Topkis's theorem.

## Depends on

- [Omnipredictors](omnipredictor.md)
- [Scoring rules and properness for finite outcomes](../../../GameTheory/mechanism-design/remaining-clauses-of-scoring-rules-and-properness.md)

## Sources

- P. Gopalan, A. T. Kalai, O. Reingold, V. Sharan, U. Wieder, "Omnipredictors", ITCS (2022), arXiv:2109.05389, Lemma 4.2 and the discussion after it ($k_\ell(v) = v$ for squared loss, $\mathbf{1}[v \ge 1/2]$ for absolute loss); the cost-sensitive and monotonicity statements are elementary.

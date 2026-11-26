# Revealment of a variable by a decision tree

For a finite set $E$, weights $\nu = (\nu_e)_{e \in E}$ with $\nu_e : \{0, 1\} \to \mathbb{R}$, a [decision tree](decision-tree.md) $T$ on $E$ and $e \in E$, the revealment of $e$ by $T$ is

$$\delta_e(T) = \mathbb{E}_\nu\big[1_{\{\omega \,:\, e \text{ is queried by } T \text{ on } \omega\}}\big],$$

the [expectation](expect.md) of the indicator that $T$ [queries](queried.md) $e$. For a [product probability weight](is-prob-weight.md) it is the probability that $T$ queries $e$.

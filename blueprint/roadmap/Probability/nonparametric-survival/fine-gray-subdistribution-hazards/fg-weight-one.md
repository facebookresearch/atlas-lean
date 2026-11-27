# Fine–Gray weights without censoring

For competing-risks data with observed times $X_i$, outcomes $\varepsilon_i$ (censored, or failure from a cause) and covariates $x_i \in \mathbb{R}^p$, the Fine–Gray risk set at $X_i$ for cause $c$ is $R^*(X_i) = \{l : X_l \ge X_i\} \cup \{l : X_l < X_i, l\text{ failed from a cause other than }c\}$. With $G \equiv 1$, the Fine–Gray weight of $l$ at $X_i$ is the indicator of $l \in R^*(X_i)$.

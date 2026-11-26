# Without competing events Fine–Gray is Cox

For competing-risks data with observed times $X_i$, outcomes $\varepsilon_i$ (censored, or failure from a cause) and covariates $x_i \in \mathbb{R}^p$, the Fine–Gray risk set at $X_i$ for cause $c$ is $R^*(X_i) = \{l : X_l \ge X_i\} \cup \{l : X_l < X_i, l\text{ failed from a cause other than }c\}$. If every subject is censored or fails from cause $c$, the Fine–Gray partial likelihood is Cox's partial likelihood.
